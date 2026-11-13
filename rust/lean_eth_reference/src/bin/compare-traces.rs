//! Strict structural equality of independently produced Lean and Rust trace streams.
//! Only the caller can authenticate their origin. This parser never supplies
//! a substitute Lean result or infers a theorem from matching finite traces.
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::Path;

type Key = (String, String);
type Records = BTreeMap<Key, Vec<String>>;

#[derive(Clone, Copy, Debug)]
enum Suite {
    High,
    Tuple,
    Layout,
    Nodes,
    Query,
}

impl Suite {
    fn parse(name: &str) -> Result<Self, String> {
        match name {
            "high" => Ok(Self::High),
            "tuple" => Ok(Self::Tuple),
            "layout" => Ok(Self::Layout),
            "nodes" => Ok(Self::Nodes),
            "query" => Ok(Self::Query),
            _ => Err(format!("unsupported trace suite: {name}")),
        }
    }

    fn expected(self) -> BTreeSet<Key> {
        let mut keys = BTreeSet::new();
        match self {
            Self::High => {
                for kind in ["branch", "initialize"] {
                    for case in ["empty", "zero", "one", "mixed", "alternate", "all"] {
                        keys.insert((kind.into(), case.into()));
                    }
                }
            }
            Self::Tuple => {
                for case in [
                    "empty", "width0", "one", "two", "split", "three", "carry", "overflow",
                ] {
                    keys.insert(("odometer".into(), case.into()));
                }
                for case in ["empty", "width0", "one", "two", "split", "three"] {
                    keys.insert(("enumerate".into(), case.into()));
                }
            }
            Self::Layout => {
                for kind in ["layout", "pair"] {
                    for case in ["0", "1", "2", "3"] {
                        keys.insert((kind.into(), case.into()));
                    }
                }
            }
            Self::Nodes => {
                for case in ["empty", "zero", "one", "two", "third", "mixed"] {
                    keys.insert(("nodes".into(), case.into()));
                }
            }
            Self::Query => {
                for case in ["empty", "none", "first", "middle", "separated", "all"] {
                    keys.insert(("prepare".into(), case.into()));
                }
            }
        }
        keys
    }
}

fn decimal(value: &str) -> bool {
    !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit())
}

fn bitword(value: &str) -> bool {
    value.bytes().all(|b| b == b'0' || b == b'1')
}

fn check(suite: Suite, fields: &[&str]) -> Result<(), &'static str> {
    let kind = fields.first().copied().unwrap_or("");
    let width = match suite {
        Suite::High => 7,
        Suite::Tuple => match kind {
            "odometer" => 8,
            "enumerate" => 9,
            _ => return Err("unexpected tuple trace kind"),
        },
        Suite::Layout => match kind {
            "layout" => 10,
            "pair" => 12,
            _ => return Err("unexpected layout trace kind"),
        },
        Suite::Nodes => 18,
        Suite::Query => 15,
    };
    if fields.len() != width {
        return Err("incorrect trace field count");
    }
    match suite {
        Suite::High => {
            if !decimal(fields[2]) || !fields[3..].iter().all(|v| bitword(v)) {
                return Err("invalid source step count or Boolean word");
            }
            let flags = if kind == "branch" { 2 } else { 1 };
            if !fields[width - flags..].iter().all(|s| s.len() == 1) {
                return Err("invalid Boolean register width");
            }
        }
        Suite::Tuple => {
            if !decimal(fields[2]) || !fields[3..].iter().all(|v| bitword(v)) {
                return Err("invalid source step count or Boolean word");
            }
            let flags: &[&str] = if kind == "odometer" {
                &fields[width - 3..]
            } else {
                &fields[width - 3..width - 1]
            };
            if !flags.iter().all(|s| s.len() == 1) {
                return Err("invalid Boolean register width");
            }
        }
        Suite::Layout => {
            if !decimal(fields[2]) || fields[2] == "0" {
                return Err("missing positive source instruction count");
            }
            if !fields[3..]
                .iter()
                .all(|v| v.bytes().all(|b| b == b'0' || b == b'1' || b == b','))
            {
                return Err("invalid Boolean word or bank delimiter");
            }
            if !fields[width - 2..].iter().all(|s| s.len() == 1) {
                return Err("invalid final register flags");
            }
            if kind == "layout"
                && (fields[3].split(',').count() != 14 || fields[4].split(',').count() != 14)
            {
                return Err("incomplete master word");
            }
            if kind == "pair" && fields[7].split(',').count() != 5 {
                return Err("incomplete pair scratch bank");
            }
        }
        Suite::Nodes => {
            if kind != "nodes" || !decimal(fields[2]) || !decimal(fields[3]) {
                return Err("invalid node trace kind or instruction counts");
            }
            if fields[2].parse::<u64>().unwrap_or(0) == 0
                || (fields[3].parse::<u64>().unwrap_or(u64::MAX) == 0) != (fields[1] == "empty")
            {
                return Err("invalid entry or reader execution count");
            }
            if !fields[4..].iter().all(|v| bitword(v))
                || !fields[14..18].iter().all(|s| s.len() == 1)
            {
                return Err("invalid physical node state or register");
            }
        }
        Suite::Query => {
            if kind != "prepare" || !decimal(fields[2]) || fields[2] == "0" {
                return Err("invalid query-prefix kind or step count");
            }
            if !fields[3..].iter().all(|v| bitword(v)) || fields[14].len() != 1 {
                return Err("invalid query-prefix word or guard register");
            }
        }
    }
    Ok(())
}

fn parse_text(suite: Suite, source: &str) -> Result<Records, String> {
    let expected = suite.expected();
    let mut observed = Records::new();
    for (index, raw) in source.lines().enumerate() {
        if raw.trim().is_empty() {
            continue;
        }
        let fields: Vec<_> = raw.trim().split('|').collect();
        if fields.len() < 2 {
            return Err(format!("line {}: missing trace key", index + 1));
        }
        let key = (fields[0].to_string(), fields[1].to_string());
        if !expected.contains(&key) {
            return Err(format!("line {}: unexpected trace key {key:?}", index + 1));
        }
        check(suite, &fields).map_err(|e| format!("line {}: {e}", index + 1))?;
        if observed
            .insert(
                key.clone(),
                fields[2..].iter().map(|s| (*s).to_string()).collect(),
            )
            .is_some()
        {
            return Err(format!("line {}: duplicate trace key {key:?}", index + 1));
        }
    }
    if observed.keys().cloned().collect::<BTreeSet<_>>() != expected {
        let missing: Vec<_> = expected
            .difference(&observed.keys().cloned().collect())
            .cloned()
            .collect();
        return Err(format!("missing trace keys: {missing:?}"));
    }
    Ok(observed)
}

fn compare(suite: Suite, lean: &str, rust: &str) -> Result<usize, String> {
    let source = parse_text(suite, lean).map_err(|e| format!("Lean trace: {e}"))?;
    let port = parse_text(suite, rust).map_err(|e| format!("Rust trace: {e}"))?;
    for (key, left) in &source {
        if port.get(key) != Some(left) {
            return Err(format!(
                "Lean/Rust divergence in {key:?}: Lean={left:?}, Rust={:?}",
                port.get(key)
            ));
        }
    }
    Ok(source.len())
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let mut suite = None;
    let mut lean = None;
    let mut rust = None;
    while let Some(flag) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("missing argument for {flag}"))?;
        match flag.as_str() {
            "--suite" => suite = Some(Suite::parse(&value)?),
            "--lean" => lean = Some(value),
            "--rust" => rust = Some(value),
            _ => return Err(format!("unknown option {flag}")),
        }
    }
    let suite = suite.ok_or("missing --suite")?;
    let lean = lean.ok_or("missing --lean")?;
    let rust = rust.ok_or("missing --rust")?;
    let lean_path = Path::new(&lean);
    let rust_path = Path::new(&rust);
    if fs::canonicalize(lean_path).map_err(|e| e.to_string())?
        == fs::canonicalize(rust_path).map_err(|e| e.to_string())?
    {
        return Err("Lean and Rust traces must come from distinct files".into());
    }
    let lean_text = fs::read_to_string(lean_path).map_err(|e| format!("Lean trace: {e}"))?;
    let rust_text = fs::read_to_string(rust_path).map_err(|e| format!("Rust trace: {e}"))?;
    let cases = compare(suite, &lean_text, &rust_text)?;
    println!(
        "PASS: {cases} exact machine trace records agree; provenance requires original Lean execution"
    );
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("compare-traces: {e}");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid(suite: Suite) -> String {
        suite
            .expected()
            .into_iter()
            .map(|(kind, case)| {
                let columns = match suite {
                    Suite::High => vec![
                        kind,
                        case,
                        "1".into(),
                        "0".into(),
                        "1".into(),
                        "0".into(),
                        "1".into(),
                    ],
                    Suite::Tuple => {
                        if kind == "odometer" {
                            vec![
                                kind,
                                case,
                                "1".into(),
                                "0".into(),
                                "0".into(),
                                "1".into(),
                                "0".into(),
                                "1".into(),
                            ]
                        } else {
                            vec![
                                kind,
                                case,
                                "1".into(),
                                "0".into(),
                                "1".into(),
                                "0".into(),
                                "1".into(),
                                "0".into(),
                                "1".into(),
                            ]
                        }
                    }
                    Suite::Layout => {
                        if kind == "layout" {
                            vec![
                                kind,
                                case,
                                "1".into(),
                                ["0"; 14].join(","),
                                ["0"; 14].join(","),
                                "0".into(),
                                "0".into(),
                                "0".into(),
                                "1".into(),
                                "0".into(),
                            ]
                        } else {
                            vec![
                                kind,
                                case,
                                "1".into(),
                                "0".into(),
                                "0".into(),
                                "0".into(),
                                "0".into(),
                                ["0"; 5].join(","),
                                "0".into(),
                                "0".into(),
                                "1".into(),
                                "0".into(),
                            ]
                        }
                    }
                    Suite::Nodes => {
                        let mut row = vec![
                            kind,
                            case.clone(),
                            "1".into(),
                            if case == "empty" { "0" } else { "1" }.into(),
                        ];
                        row.extend(vec!["0".into(); 14]);
                        row
                    }
                    Suite::Query => {
                        let mut row = vec![kind, case, "1".into()];
                        row.extend(vec!["0".into(); 12]);
                        row
                    }
                };
                columns.join("|")
            })
            .collect::<Vec<_>>()
            .join("\n")
            + "\n"
    }

    #[test]
    fn each_suite_requires_complete_validated_records() {
        for suite in [
            Suite::High,
            Suite::Tuple,
            Suite::Layout,
            Suite::Nodes,
            Suite::Query,
        ] {
            let original = valid(suite);
            let count = compare(suite, &original, &original).unwrap();
            assert_eq!(count, suite.expected().len());
            assert!(
                parse_text(
                    suite,
                    &original.lines().skip(1).collect::<Vec<_>>().join("\n")
                )
                .is_err()
            );
            assert!(parse_text(suite, &(original.clone() + &original)).is_err());
            assert!(
                compare(
                    suite,
                    &original,
                    &(original.clone() + "extraneous|case|1\n")
                )
                .is_err()
            );
        }
    }

    #[test]
    fn changed_physical_word_cannot_pass() {
        for suite in [
            Suite::High,
            Suite::Tuple,
            Suite::Layout,
            Suite::Nodes,
            Suite::Query,
        ] {
            let original = valid(suite);
            let mut rows: Vec<_> = original.lines().map(str::to_owned).collect();
            let mut fields: Vec<_> = rows[0].split('|').map(str::to_owned).collect();
            let last = fields.len() - 1;
            fields[last] = "1".into();
            rows[0] = fields.join("|");
            if rows[0] == original.lines().next().unwrap() {
                fields[last] = "0".into();
                rows[0] = fields.join("|");
            }
            let changed = rows.join("\n");
            assert!(compare(suite, &original, &changed).is_err());
        }
    }

    #[test]
    fn invalid_schema_cannot_be_accepted() {
        for suite in [
            Suite::High,
            Suite::Tuple,
            Suite::Layout,
            Suite::Nodes,
            Suite::Query,
        ] {
            let source = valid(suite);
            let mut lines: Vec<_> = source.lines().map(str::to_owned).collect();
            lines[0].push_str("|unexpected");
            assert!(parse_text(suite, &lines.join("\n")).is_err());
            assert!(parse_text(suite, &source.replacen("|1|", "|bad|", 1)).is_err());
        }
    }
}
