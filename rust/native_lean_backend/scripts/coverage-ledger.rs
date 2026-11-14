//! Reject source/coverage drift using the actual pinned Lean inductive
//! constructor inventory (from IRInventory.lean). No compiler IR is serialized.
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::error::Error;
use std::fs;

#[derive(Debug)]
struct Classification {
    tag: usize,
    status: String,
    scope: String,
    evidence: String,
}

fn cells<'a>(line: &'a str, width: usize) -> Result<Vec<&'a str>, String> {
    let values: Vec<_> = line.split('\t').collect();
    if values.len() != width || values.iter().any(|cell| cell.is_empty()) {
        return Err(format!("expected {width} nonempty TSV cells: {line}"));
    }
    Ok(values)
}

fn run(inventory: &str, classification: &str) -> Result<String, String> {
    let mut classes = BTreeMap::new();
    for line in classification.lines().filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let row = cells(line, 5)?;
        let tag: usize = row[1].parse().map_err(|_| format!("invalid tag in {line}"))?;
        if !matches!(row[2], "implemented_bounded" | "explicitly_unsupported") {
            return Err(format!("unknown coverage status: {}", row[2]));
        }
        if classes.insert(row[0], Classification {
            tag,
            status: row[2].to_string(),
            scope: row[3].to_string(),
            evidence: row[4].to_string(),
        }).is_some() {
            return Err(format!("duplicate classification: {}", row[0]));
        }
    }

    let mut rows = Vec::new();
    let mut families = BTreeSet::new();
    let mut observed = BTreeSet::new();
    let mut supported = 0;
    for line in inventory.lines().skip(1).filter(|l| !l.is_empty()) {
        let row = cells(line, 3)?;
        let family = row[0];
        let constructor = row[1];
        let tag: usize = row[2].parse().map_err(|_| format!("invalid runtime tag in {line}"))?;
        if !constructor.starts_with(&format!("{family}.")) {
            return Err(format!("constructor {constructor} not in family {family}"));
        }
        if !observed.insert(constructor) {
            return Err(format!("duplicate runtime IR constructor: {constructor}"));
        }
        let classification = classes
            .get(constructor)
            .ok_or_else(|| format!("unclassified pinned Lean IR constructor: {constructor}"))?;
        if tag != classification.tag {
            return Err(format!(
                "ABI tag drift for {constructor}: Lean says {tag}, contract says {}",
                classification.tag
            ));
        }
        families.insert(family);
        if classification.status == "implemented_bounded" {
            supported += 1;
        }
        rows.push(format!(
            "{family}\t{constructor}\t{tag}\t{}\t{}\t{}",
            classification.status, classification.scope, classification.evidence
        ));
    }
    if observed.len() != classes.len() {
        let missing: Vec<_> = classes.keys().filter(|k| !observed.contains(**k)).collect();
        return Err(format!("classification has obsolete constructors: {missing:?}"));
    }
    if families.len() != 7 {
        return Err(format!("expected seven IR inductive families, got {}", families.len()));
    }
    let mut output = String::from("family\tconstructor\ttag\tstatus\tscope\tevidence\n");
    output.push_str(&rows.join("\n"));
    output.push('\n');
    eprintln!(
        "Pinned Lean IR inventory: {} families, {} constructors, {} bounded implemented, {} explicitly unsupported",
        families.len(),
        rows.len(),
        supported,
        rows.len() - supported
    );
    Ok(output)
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 4 {
        return Err("usage: coverage-ledger <derived-inventory.tsv> <coverage-classification.tsv> <output.tsv>".into());
    }
    let inventory = fs::read_to_string(&args[1])?;
    let classification = fs::read_to_string(&args[2])?;
    let result = run(&inventory, &classification)?;
    fs::write(&args[3], result)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::run;

    #[test]
    fn rejects_constructor_and_tag_drift() {
        let original = "family\tconstructor\ttag\nLean.IR.Expr\tLean.IR.Expr.fap\t6\n";
        let supported = "Lean.IR.Expr.fap\t6\timplemented_bounded\tprimitives\tconformance\n";
        assert!(run(original, supported).unwrap_err().contains("seven IR inductive"));
        let changed = "family\tconstructor\ttag\nLean.IR.Expr\tLean.IR.Expr.fap\t5\n";
        assert!(run(changed, supported).unwrap_err().contains("ABI tag drift"));
        let unknown = "family\tconstructor\ttag\nLean.IR.Expr\tLean.IR.Expr.future\t7\n";
        assert!(run(unknown, supported).unwrap_err().contains("unclassified"));
    }
}
