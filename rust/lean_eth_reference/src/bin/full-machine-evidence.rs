//! Original-source full machine trace comparison, profiling, and evidence receipts.
//! No Lean execution is simulated here. The upstream runner owns provenance.
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

type Fallible<T> = Result<T, String>;
const CASES: usize = 62;

#[derive(Clone, Debug, PartialEq, Eq)]
struct State {
    step: usize,
    pc: String,
    regs: String,
    left: String,
    right: String,
}
type Traces = BTreeMap<String, Vec<State>>;

fn decimal(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}
fn bits(s: &str) -> bool {
    s.bytes().all(|b| b == b'0' || b == b'1')
}
fn names() -> BTreeSet<String> {
    (0..5)
        .flat_map(|size| {
            (0..(1 << size)).flat_map(move |code| {
                ["clean", "dirty"].map(move |mode| format!("{size}_{code}_{mode}"))
            })
        })
        .collect()
}
fn parse(source: &str) -> Fallible<Traces> {
    let valid = names();
    let mut result: Traces = BTreeMap::new();
    for (line_no, line) in source.lines().enumerate() {
        let cols: Vec<_> = line.split('|').collect();
        if cols.len() != 7 || cols[0] != "machine" {
            return Err(format!(
                "line {}: expected seven machine fields",
                line_no + 1
            ));
        }
        let [_, name, step, pc, regs, left, right] =
            <[&str; 7]>::try_from(cols.as_slice()).map_err(|_| "malformed machine record")?;
        if !valid.contains(name)
            || !decimal(step)
            || (pc != "H" && !decimal(pc))
            || regs.len() != 2
            || !bits(regs)
            || !bits(left)
            || !bits(right)
        {
            return Err(format!(
                "line {}: invalid case, step, PC, register or stack bits",
                line_no + 1
            ));
        }
        let step = step.parse::<usize>().map_err(|_| "step overflow")?;
        let sequence = result.entry(name.to_owned()).or_default();
        if step != sequence.len() || sequence.last().is_some_and(|s| s.pc == "H") {
            return Err(format!(
                "line {}: repeated, skipped or post-halt step",
                line_no + 1
            ));
        }
        sequence.push(State {
            step,
            pc: pc.to_owned(),
            regs: regs.to_owned(),
            left: left.to_owned(),
            right: right.to_owned(),
        });
    }
    if result.keys().cloned().collect::<BTreeSet<_>>() != valid {
        return Err("incomplete or unexpected complete-machine case set".into());
    }
    for (case, states) in &result {
        if states.len() < 2
            || states.last().is_none_or(|s| s.pc != "H")
            || states[..states.len() - 1].iter().any(|s| s.pc == "H")
        {
            return Err(format!("{case}: missing, early or repeated halt"));
        }
    }
    Ok(result)
}
fn read(path: &Path) -> Fallible<Traces> {
    parse(&fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?)
}
fn compare(lean: &Traces, rust: &Traces) -> Fallible<usize> {
    for (name, ls) in lean {
        let rs = rust
            .get(name)
            .ok_or_else(|| format!("missing Rust case {name}"))?;
        for (step, (a, b)) in ls.iter().zip(rs).enumerate() {
            if a != b {
                return Err(format!(
                    "{name} instruction {step}: source Lean={a:?}, Rust={b:?}"
                ));
            }
        }
        if ls.len() != rs.len() {
            return Err(format!("{name}: different instruction counts"));
        }
    }
    Ok(lean.values().map(Vec::len).sum())
}
fn distinct(a: &Path, b: &Path) -> Fallible<()> {
    let left = fs::canonicalize(a).map_err(|e| e.to_string())?;
    let right = fs::canonicalize(b).map_err(|e| e.to_string())?;
    if left == right {
        return Err("Lean and Rust traces must be different files".into());
    }
    Ok(())
}
fn transition(a: &State, b: &State) -> bool {
    let mut changed = 0;
    for (old, new) in [(&a.left, &b.left), (&a.right, &b.right)] {
        if old == new {
            continue;
        }
        changed += 1;
        if !(new.get(1..) == Some(old.as_str()) || old.get(1..) == Some(new.as_str())) {
            return false;
        }
    }
    changed <= 1
}
#[derive(Debug, Clone, PartialEq, Eq)]
struct Profile {
    transitions: usize,
    states: usize,
    peak_bits: usize,
    final_regs: String,
    final_output: String,
}
fn profiles(traces: &Traces) -> Fallible<BTreeMap<String, Profile>> {
    let mut result = BTreeMap::new();
    for (name, states) in traces {
        for (before, after) in states.iter().zip(states.iter().skip(1)) {
            if !transition(before, after) {
                return Err(format!(
                    "{name}: impossible physical stack transition at {}",
                    before.step
                ));
            }
        }
        let final_state = states.last().ok_or("empty trace")?;
        result.insert(
            name.clone(),
            Profile {
                transitions: states.len() - 1,
                states: states.len(),
                peak_bits: states
                    .iter()
                    .map(|s| s.left.len() + s.right.len())
                    .max()
                    .unwrap_or(0),
                final_regs: final_state.regs.clone(),
                final_output: final_state.right.clone(),
            },
        );
    }
    Ok(result)
}
fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c <= '\u{1f}' => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
fn profile_json(p: &BTreeMap<String, Profile>) -> String {
    let mut cases = Vec::new();
    for (case, v) in p {
        cases.push(format!("{}:{{\"source_transitions\":{},\"states_observed\":{},\"halted\":true,\"peak_live_stack_bits\":{},\"final_regs\":{},\"final_output_stack\":{}}}",
            quote(case), v.transitions, v.states, v.peak_bits, quote(&v.final_regs), quote(&v.final_output)));
    }
    format!("{{{}}}", cases.join(","))
}
const CSV_FIELDS: [&str; 10] = [
    "case",
    "opcode",
    "transitions",
    "elapsed_ns",
    "allocation_calls",
    "reallocation_calls",
    "requested_bytes",
    "peak_stack_bits",
    "peak_stack_capacity_bits",
    "max_integer_bits",
];
type NativeCase = (BTreeMap<String, u128>, BTreeMap<String, String>);
const ACCOUNTS: [&str; 5] = [
    "transitions",
    "elapsed_ns",
    "allocation_calls",
    "reallocation_calls",
    "requested_bytes",
];
const OPCODES: [&str; 12] = [
    "halt", "goto", "set", "copy", "not", "and", "or", "xor", "branch", "push", "peek", "pop",
];
fn native_metrics(path: &Path, profiles: &BTreeMap<String, Profile>) -> Fallible<String> {
    let data = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut rows = data.lines();
    let header = rows.next().ok_or("empty profiler CSV")?;
    let header: Vec<_> = header.split(',').collect();
    if header.len() != CSV_FIELDS.len() || CSV_FIELDS.iter().any(|s| !header.contains(s)) {
        return Err("invalid native profiler CSV header".into());
    }
    let mut record: BTreeMap<String, NativeCase> = BTreeMap::new();
    for (line_no, line) in rows.enumerate() {
        let fields: Vec<_> = line.split(',').collect();
        if fields.len() != CSV_FIELDS.len() {
            return Err(format!("invalid CSV line {}", line_no + 2));
        }
        let get = |key: &str| -> Fallible<&str> {
            let i = header
                .iter()
                .position(|&x| x == key)
                .ok_or("missing header")?;
            Ok(fields[i])
        };
        let case = get("case")?;
        let op = get("opcode")?;
        let p = profiles.get(case).ok_or("unknown profiler case")?;
        if !OPCODES.contains(&op) {
            return Err(format!("unknown profiler opcode {op}"));
        }
        let entry = record
            .entry(case.into())
            .or_insert_with(|| (BTreeMap::new(), BTreeMap::new()));
        if entry.1.contains_key(op) {
            return Err(format!("duplicate profiler case/opcode {case}/{op}"));
        }
        let mut values = BTreeMap::new();
        for key in ACCOUNTS {
            let num = get(key)?;
            if !decimal(num) {
                return Err(format!("{case}/{op}: nonnumeric {key}"));
            }
            values.insert(
                key,
                num.parse::<u128>()
                    .map_err(|_| "profiler number overflow")?,
            );
        }
        if values["transitions"] == 0 || get("max_integer_bits")? != "NA" {
            return Err(format!("{case}/{op}: invalid transitions or bit-width"));
        }
        let live = get("peak_stack_bits")?
            .parse::<usize>()
            .map_err(|_| "invalid peak")?;
        let capacity = get("peak_stack_capacity_bits")?
            .parse::<usize>()
            .map_err(|_| "invalid stack capacity")?;
        if live != p.peak_bits || capacity < live {
            return Err(format!("{case}/{op}: peak mismatch"));
        }
        let by_opcode = format!(
            "{{{}}}",
            ACCOUNTS
                .iter()
                .map(|k| format!("{}:{}", quote(k), values[k]))
                .collect::<Vec<_>>()
                .join(",")
        );
        for key in ACCOUNTS {
            let v = entry.0.entry(key.into()).or_insert(0);
            *v = v
                .checked_add(values[key])
                .ok_or("profiler total overflow")?;
        }
        entry.1.insert(op.into(), by_opcode);
    }
    if record.len() != profiles.len() {
        return Err("incomplete profiler case coverage".into());
    }
    let mut cases = Vec::new();
    for (case, (totals, ops)) in record {
        if totals["transitions"] != profiles[&case].transitions as u128 {
            return Err(format!("{case}: transition accounting mismatch"));
        }
        let mut fields = ACCOUNTS
            .iter()
            .map(|k| format!("{}:{}", quote(k), totals[*k]))
            .collect::<Vec<_>>();
        fields.push(format!(
            "\"by_opcode\":{{{}}}",
            ops.into_iter()
                .map(|(op, v)| format!("{}:{v}", quote(&op)))
                .collect::<Vec<_>>()
                .join(",")
        ));
        cases.push(format!("{}:{{{}}}", quote(&case), fields.join(",")));
    }
    Ok(format!("{{{}}}", cases.join(",")))
}
fn write_file(path: &Path, content: &str) -> Fallible<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    fs::write(path, content).map_err(|e| e.to_string())
}
fn output_profile(
    rust: &Path,
    lean: Option<&Path>,
    metrics: Option<&Path>,
    output: &Path,
) -> Fallible<()> {
    let port = read(rust)?;
    let p = profiles(&port)?;
    let lean_profile = if let Some(path) = lean {
        distinct(path, rust)?;
        let upstream = read(path)?;
        compare(&upstream, &port)?;
        let lp = profiles(&upstream)?;
        if lp != p {
            return Err("Lean/Rust profile divergence".into());
        }
        Some(lp)
    } else {
        None
    };
    let native = if let Some(path) = metrics {
        native_metrics(path, &p)?
    } else {
        "null".into()
    };
    let status = if lean.is_some() {
        "INDEPENDENT_LEAN_RUST_MATCH"
    } else {
        "RUST_ONLY_NOT_DIFFERENTIAL"
    };
    let report = format!(
        concat!(
            "{{\"status\":{},\"measurement_scope\":\"BitProgram source instructions, not primitive TM2 steps\",",
            "\"theorem_tm2_resource_bound_verified\":false,",
            "\"timing_note\":\"instrumented Rust elapsed_ns includes observer overhead; Lean per-op timing is unobserved\",",
            "\"allocation_note\":\"Rust allocations are alloc/realloc requests made during step(); not net heap bytes or Lean allocations\",",
            "\"integer_note\":\"No host big integers exist in this Boolean source machine; max integer bits not applicable\",",
            "\"rust_source_states\":{},\"lean_source_states\":{},\"rust_native_op_metrics\":{}}}\n"
        ),
        quote(status),
        profile_json(&p),
        lean_profile.as_ref().map_or("null".into(), profile_json),
        native
    );
    write_file(output, &report)?;
    println!("{status}: {} cases; report={}", p.len(), output.display());
    Ok(())
}
fn sha256(path: &Path) -> Fallible<(String, u64)> {
    let result = Command::new("sha256sum")
        .arg("--")
        .arg(path)
        .output()
        .map_err(|e| e.to_string())?;
    if !result.status.success() {
        return Err(format!("sha256sum failed on {}", path.display()));
    }
    let digest = String::from_utf8(result.stdout)
        .map_err(|e| e.to_string())?
        .split_whitespace()
        .next()
        .ok_or("empty sha256sum")?
        .to_string();
    if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid SHA-256 digest".into());
    }
    let len = fs::metadata(path).map_err(|e| e.to_string())?.len();
    Ok((digest, len))
}
fn entry(path: &Path) -> Fallible<String> {
    let (digest, len) = sha256(path)?;
    Ok(format!("{{\"sha256\":{},\"bytes\":{len}}}", quote(&digest)))
}
fn receipt(
    out: &Path,
    source: &str,
    mathlib: &str,
    lean: &str,
    rust: &str,
    head: &str,
    suites: &[String],
) -> Fallible<()> {
    let mut all = BTreeMap::new();
    if suites.is_empty() {
        return Err("no completed suites for receipt".into());
    }
    for suite in suites {
        if !["full", "high", "tuple", "layout", "nodes", "query"].contains(&suite.as_str())
            || all.contains_key(suite)
        {
            return Err(format!("unknown or duplicate suite {suite}"));
        }
        let mut fields = vec![
            format!(
                "\"lean\":{}",
                entry(&out.join(format!("{suite}.lean.trace")))?
            ),
            format!(
                "\"rust\":{}",
                entry(&out.join(format!("{suite}.rust.trace")))?
            ),
        ];
        if suite == "full" {
            fields.push(format!(
                "\"rust_opcode_profile\":{}",
                entry(&out.join("full.rust.ops.csv"))?
            ));
            fields.push(format!(
                "\"state_resource_profile\":{}",
                entry(&out.join("full.profile.json"))?
            ));
        }
        all.insert(suite.clone(), format!("{{{}}}", fields.join(",")));
    }
    let provenance = format!(
        "{{\"openai_math_commit\":{},\"mathlib_commit\":{},\"lean\":{},\"rust\":{},\"rust_commit\":{}}}",
        quote(source),
        quote(mathlib),
        quote(lean),
        quote(rust),
        quote(head)
    );
    let suites_json = all
        .into_iter()
        .map(|(k, v)| format!("{}:{v}", quote(&k)))
        .collect::<Vec<_>>()
        .join(",");
    let contents = format!(
        "{{\"status\":\"PASS\",\"provenance\":{provenance},\"suites\":{{{suites_json}}}}}\n"
    );
    let temp = out.join("receipt.json.tmp");
    write_file(&temp, &contents)?;
    fs::rename(&temp, out.join("receipt.json")).map_err(|e| e.to_string())?;
    println!(
        "PASS: {} genuine imported-Lean differential suites",
        suites.len()
    );
    Ok(())
}
fn flag(args: &[String], name: &str) -> Option<String> {
    args.windows(2).find(|w| w[0] == name).map(|w| w[1].clone())
}
fn required(args: &[String], name: &str) -> Fallible<String> {
    flag(args, name).ok_or_else(|| format!("missing {name}"))
}
fn run() -> Fallible<()> {
    let mut args = env::args().skip(1);
    let action = args.next().ok_or("expected compare|profile|receipt")?;
    let rest: Vec<_> = args.collect();
    match action.as_str() {
        "compare" => {
            let lean = PathBuf::from(required(&rest, "--lean")?);
            let rust = PathBuf::from(required(&rest, "--rust")?);
            distinct(&lean, &rust)?;
            let cases = compare(&read(&lean)?, &read(&rust)?)?;
            println!(
                "Matched full machine traces: {CASES} cases, {cases} states (provenance enforced by caller)"
            );
            Ok(())
        }
        "profile" => output_profile(
            &PathBuf::from(required(&rest, "--rust")?),
            flag(&rest, "--lean").map(PathBuf::from).as_deref(),
            flag(&rest, "--rust-metrics").map(PathBuf::from).as_deref(),
            &PathBuf::from(required(&rest, "--output")?),
        ),
        "receipt" => {
            let suite_names = rest
                .windows(2)
                .filter(|w| w[0] == "--suite")
                .map(|w| w[1].clone())
                .collect::<Vec<_>>();
            receipt(
                &PathBuf::from(required(&rest, "--output-dir")?),
                &required(&rest, "--source")?,
                &required(&rest, "--mathlib")?,
                &required(&rest, "--lean-version")?,
                &required(&rest, "--rust-version")?,
                &required(&rest, "--rust-commit")?,
                &suite_names,
            )
        }
        _ => Err(format!("unknown action {action}")),
    }
}
fn main() {
    if let Err(e) = run() {
        eprintln!("full-machine-evidence: {e}");
        std::process::exit(2);
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> String {
        let mut out = String::new();
        for name in names() {
            out.push_str(&format!(
                "machine|{name}|0|0|00||\nmachine|{name}|1|H|00||\n"
            ));
        }
        out
    }
    #[test]
    fn full_state_comparison_rejects_mutations() {
        let a = fixture();
        let good = parse(&a).unwrap();
        assert_eq!(good.len(), 62);
        assert_eq!(compare(&good, &good).unwrap(), 124);
        assert!(parse(&a.replacen("machine|0_0_clean|1|H|", "machine|0_0_clean|2|H|", 1)).is_err());
        assert!(parse(&a.replacen("machine|0_0_clean|1|H|", "machine|0_0_clean|1|1|", 1)).is_err());
        assert!(parse(&a.lines().skip(2).collect::<Vec<_>>().join("\n")).is_err());
        let modified = a.replacen(
            "machine|0_0_clean|0|0|00||",
            "machine|0_0_clean|0|0|10||",
            1,
        );
        assert!(compare(&good, &parse(&modified).unwrap()).is_err());
    }
    #[test]
    fn impossible_stack_changes_reject() {
        let a = fixture();
        assert!(profiles(&parse(&a).unwrap()).is_ok());
        for new in [
            "machine|0_0_clean|1|H|00|11|",
            "machine|0_0_clean|1|H|00|1|0",
        ] {
            let changed = a.replace("machine|0_0_clean|1|H|00||", new);
            assert!(profiles(&parse(&changed).unwrap()).is_err());
        }
    }
    #[test]
    fn csv_rejects_missing_and_wrong_accounting() {
        let traces = profiles(&parse(&fixture()).unwrap()).unwrap();
        let path = env::temp_dir().join(format!("eth-metrics-{}.csv", std::process::id()));
        fs::write(&path, CSV_FIELDS.join(",")).unwrap();
        assert!(native_metrics(&path, &traces).is_err());
        fs::remove_file(path).unwrap();
    }
}
