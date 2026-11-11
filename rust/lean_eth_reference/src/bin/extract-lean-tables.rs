//! Deterministic scanner for original pinned Lean literal finite programs.
//! Only fixed numeric tables/matches/finite conditionals are accepted.
//! No Lean expression evaluator, synthesized instructions, or source-parity claim.
#[path = "../../tools/lean_table_codegen.rs"]
mod lean_table_codegen;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const SOURCE: &str = "4eaee87548250b2682affda7d05d947c05554bae";
const BASE: &str = "lean/OAI/Algorithms/SubexponentialSAT";
type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
struct SourceDecl {
    name: String,
    r: usize,
    s: usize,
    labels: usize,
    input: usize,
    output: usize,
    entry: usize,
    body: Vec<String>,
    ordinal: usize,
}
#[derive(Clone, Debug)]
struct Extracted {
    id: String,
    file: String,
    blob: String,
    r: usize,
    s: usize,
    labels: usize,
    entry: usize,
    input: usize,
    output: usize,
    table: String,
}
fn num(s: &str) -> Result<usize> {
    if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) || (s.starts_with('0') && s.len() > 1)
    {
        return Err(format!("noncanonical number {s:?}"));
    }
    s.parse().map_err(|_| format!("number overflow {s:?}"))
}
fn hash_with(program: &str, args: &[&str], bytes: &[u8]) -> Result<String> {
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("required {program}: {e}"))?;
    child
        .stdin
        .take()
        .ok_or("cannot pipe hash input")?
        .write_all(bytes)
        .map_err(|e| e.to_string())?;
    let output = child.wait_with_output().map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(format!("{program} failed to hash source"));
    }
    let text = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    let digest = text
        .split_whitespace()
        .next()
        .ok_or("missing hash digest")?;
    let size = if program == "git" { 40 } else { 64 };
    if digest.len() != size || !digest.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err(format!("invalid {program} hash"));
    }
    Ok(digest.to_string())
}
fn git_blob(bytes: &[u8]) -> Result<String> {
    hash_with("git", &["hash-object", "--stdin"], bytes)
}
fn sha256(bytes: &[u8]) -> Result<String> {
    hash_with("sha256sum", &[], bytes)
}

fn symbol_table(prefix: &str, labels: usize) -> BTreeMap<String, usize> {
    let mut symbols = BTreeMap::new();
    for line in prefix.lines() {
        let t = line.trim();
        if !t.starts_with("def ") {
            continue;
        }
        let Some((left, right)) = t.split_once(": Fin ") else {
            continue;
        };
        let Some((domain, val)) = right.split_once(":=") else {
            continue;
        };
        if let (Ok(n), Ok(v)) = (num(domain.trim()), num(val.trim()))
            && n == labels
            && v < labels
            && let Some(name) = left.split_whitespace().nth(1)
        {
            symbols.insert(name.to_string(), v);
        }
    }
    symbols
}
fn instruction(raw: &str, symbols: &BTreeMap<String, usize>) -> Result<String> {
    let trimmed = raw.trim();
    let Some(part) = trimmed.strip_prefix('.') else {
        return Err(format!("unsupported instruction {raw:?}"));
    };
    let toks: Vec<_> = part.split_whitespace().collect();
    let Some(&op) = toks.first() else {
        return Err("empty opcode".into());
    };
    let arity = match op {
        "halt" => 0,
        "goto" => 1,
        "set" | "copy" | "bnot" | "push" => 3,
        "band" | "bor" | "bxor" | "peek" | "pop" => 4,
        "branch" => 3,
        _ => return Err(format!("unknown Lean opcode {op}")),
    };
    if toks.len() != arity + 1 {
        return Err(format!("{op}: incorrect operand count"));
    }
    let mut args = Vec::new();
    for (index, &word) in toks[1..].iter().enumerate() {
        let v = if op == "set" && index == 1 {
            match word {
                "true" => 1,
                "false" => 0,
                _ => {
                    if let Some(&v) = symbols.get(word) {
                        v
                    } else {
                        num(word)?
                    }
                }
            }
        } else if let Some(v) = symbols.get(word) {
            *v
        } else {
            num(word)?
        };
        args.push(v.to_string());
    }
    let opcode = match op {
        "bnot" => "not",
        "band" => "and",
        "bor" => "or",
        "bxor" => "xor",
        other => other,
    };
    Ok(std::iter::once(opcode.to_string())
        .chain(args)
        .collect::<Vec<_>>()
        .join(":"))
}
fn parse_header(line: &str) -> Option<(String, usize, usize, usize)> {
    let first = line
        .strip_prefix("def ")
        .or_else(|| line.strip_prefix("abbrev "))?;
    let (name, tail) = first.split_once(" : ")?;
    if !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
        return None;
    }
    let mut parts = tail.split_whitespace().collect::<Vec<_>>();
    if parts.len() != 5 || *parts.last()? != "where" || !parts[0].ends_with("Program") {
        return None;
    }
    parts.remove(0);
    let r = num(parts[0]).ok()?;
    let s = num(parts[1]).ok()?;
    let labels = num(parts[2]).ok()?;
    Some((name.to_string(), r, s, labels))
}
fn field(line: &str, name: &str) -> Result<usize> {
    let prefix = format!("{name} :=");
    num(line
        .trim()
        .strip_prefix(&prefix)
        .ok_or_else(|| format!("missing {name}"))?
        .trim())
}
fn declarations(source: &str) -> Result<(Vec<SourceDecl>, Vec<String>)> {
    let lines: Vec<_> = source.lines().collect();
    let mut decls = Vec::new();
    let mut failures = Vec::new();
    for i in 0..lines.len() {
        let Some((name, r, s, labels)) = parse_header(lines[i]) else {
            continue;
        };
        if i + 4 >= lines.len() {
            return Err(format!("{name}: truncated finite declaration"));
        }
        let input = field(lines[i + 1], "inputStack")?;
        let output = field(lines[i + 2], "outputStack")?;
        let entry = field(lines[i + 3], "entry")?;
        let code = lines[i + 4].trim();
        let legacy =
            code.starts_with("code := ![") || code.starts_with("code q := match q.val with");
        if !code.starts_with("code := ![")
            && !(code.starts_with("code ") && code.contains(" := match "))
            && !code.starts_with("code := fun ")
        {
            continue;
        }
        let mut body = Vec::new();
        let mut j = i + 4;
        while j < lines.len() {
            // Code arms are indented; stop before the next top-level definition or proof.
            if j > i + 4
                && !lines[j].trim().is_empty()
                && !lines[j].starts_with(' ')
                && !lines[j].starts_with('\t')
            {
                break;
            }
            if j > i + 4 && lines[j].trim().is_empty() {
                break;
            }
            body.push(lines[j].to_string());
            j += 1;
        }
        let symbols = symbol_table(&lines[..i].join("\n"), labels);
        let instructions = match parse_code(&body, labels, &symbols) {
            Ok(x) => x,
            Err(e) => {
                failures.push(format!("{name}: {e}"));
                continue;
            }
        };
        // Store source instructions now, no semantic interpretation of Lean.
        decls.push((
            name,
            r,
            s,
            labels,
            input,
            output,
            entry,
            legacy,
            instructions,
        ));
    }
    let legacy_count = decls.iter().filter(|item| item.7).count();
    let mut legacy_position = 0;
    let mut new_position = legacy_count;
    let result = decls
        .into_iter()
        .map(|(name, r, s, labels, input, output, entry, legacy, body)| {
            let ordinal = if legacy {
                let n = legacy_position;
                legacy_position += 1;
                n
            } else {
                let n = new_position;
                new_position += 1;
                n
            };
            SourceDecl {
                name,
                r,
                s,
                labels,
                input,
                output,
                entry,
                body,
                ordinal,
            }
        })
        .collect();
    Ok((result, failures))
}
fn parse_code(
    lines: &[String],
    labels: usize,
    symbols: &BTreeMap<String, usize>,
) -> Result<Vec<String>> {
    let head = lines.first().ok_or("missing code")?.trim();
    let mut output = Vec::new();
    if let Some(first) = head.strip_prefix("code := ![") {
        let all = std::iter::once(first)
            .chain(lines.iter().skip(1).map(|s| s.as_str()))
            .collect::<Vec<_>>()
            .join("\n");
        let (items, trailing) = all.split_once(']').ok_or("unclosed fixed vector")?;
        if !trailing.trim().is_empty() {
            return Err("code after literal vector".into());
        }
        for item in items.split(',') {
            output.push(instruction(item, symbols)?);
        }
    } else if head.starts_with("code ")
        && head.contains(" := match ")
        && head.ends_with(".val with")
    {
        let (var, matcher) = head
            .strip_prefix("code ")
            .ok_or("not code")?
            .split_once(" := match ")
            .ok_or("missing match")?;
        if matcher != format!("{var}.val with") {
            return Err("match variable mismatch".into());
        }
        let mut seen = BTreeMap::new();
        let mut fallback = None;
        let mut arms = 0;
        for line in lines.iter().skip(1) {
            let t = line.trim();
            let Some(rem) = t.strip_prefix("| ") else {
                return Err("unsupported label match arm".into());
            };
            let (label, expr) = rem.split_once(" => ").ok_or("invalid match arm")?;
            let inst = instruction(expr, symbols)?;
            if label == "_" {
                if fallback.is_some() {
                    return Err("duplicate fallback".into());
                }
                fallback = Some(inst);
            } else {
                if fallback.is_some() {
                    return Err("fallback must be last".into());
                }
                let n = num(label)?;
                if n >= labels || seen.insert(n, inst).is_some() {
                    return Err("duplicate/out-of-range label".into());
                }
            }
            arms += 1;
        }
        if arms == 0 {
            return Err("empty match".into());
        }
        if fallback.is_none() && seen.len() != labels {
            return Err("incomplete match without fallback".into());
        }
        for index in 0..labels {
            output.push(
                seen.get(&index)
                    .cloned()
                    .or_else(|| fallback.clone())
                    .ok_or("missing finite label")?,
            );
        }
    } else if let Some(tail) = head.strip_prefix("code := fun ") {
        let (var, first) = tail.split_once(" => ").ok_or("invalid finite lambda")?;
        let expr = std::iter::once(first)
            .chain(lines.iter().skip(1).map(|s| s.as_str()))
            .collect::<Vec<_>>()
            .join(" ");
        let mut pending = expr.split_whitespace().collect::<Vec<_>>();
        let mut index = 0;
        while pending.first() == Some(&"if") {
            if pending.len() < 7 || pending[1] != var || pending[2] != "=" || pending[4] != "then" {
                return Err("unsupported finite conditional".into());
            }
            if num(pending[3])? != index {
                return Err("nonconsecutive conditional labels".into());
            }
            let else_index = pending
                .iter()
                .position(|&t| t == "else")
                .ok_or("conditional missing else")?;
            output.push(instruction(&pending[5..else_index].join(" "), symbols)?);
            pending = pending[else_index + 1..].to_vec();
            index += 1;
        }
        let fallback = instruction(&pending.join(" "), symbols)?;
        if output.len() > labels {
            return Err("too many finite labels".into());
        }
        output.resize(labels, fallback);
    } else {
        return Err("unsupported nonliteral code constructor".into());
    }
    if output.len() != labels {
        return Err(format!("label count {} != {labels}", output.len()));
    }
    Ok(output)
}
fn source_files(root: &Path) -> Result<Vec<PathBuf>> {
    let mut all = Vec::new();
    let mut waiting = vec![root.to_path_buf()];
    while let Some(dir) = waiting.pop() {
        for item in fs::read_dir(dir).map_err(|e| e.to_string())? {
            let p = item.map_err(|e| e.to_string())?.path();
            if p.is_dir() {
                waiting.push(p);
            } else if p.extension().is_some_and(|e| e == "lean") {
                all.push(p);
            }
        }
    }
    all.sort();
    Ok(all)
}
fn table(e: &Extracted) -> String {
    let mut out = format!(
        "PIN|{}|{}|{}\nPROGRAM|{}|{}|{}|{}|{}|{}|{}\n",
        e.id, SOURCE, e.blob, e.id, e.r, e.s, e.labels, e.entry, e.input, e.output
    );
    for (i, code) in e.table.lines().enumerate() {
        out.push_str(&format!("CODE|{}|{}|{}\n", e.id, i, code));
    }
    out.push_str(&format!("END|{}|{}\n", e.id, e.labels));
    out
}
fn extract(root: &Path) -> Result<(Vec<Extracted>, Vec<String>)> {
    let mut entries = Vec::new();
    let mut failures = Vec::new();
    let base = root.join(BASE);
    for path in source_files(&base)? {
        let data = fs::read(&path).map_err(|e| e.to_string())?;
        let source = String::from_utf8(data.clone()).map_err(|e| e.to_string())?;
        let source_path = path
            .strip_prefix(root)
            .map_err(|e| e.to_string())?
            .to_string_lossy()
            .replace('\\', "/");
        let blob = git_blob(&data)?;
        let relative = path
            .strip_prefix(&base)
            .map_err(|e| e.to_string())?
            .with_extension("")
            .to_string_lossy()
            .replace('\\', "/")
            .replace(['/', '.'], "_")
            .to_lowercase();
        match declarations(&source) {
            Ok((decls, source_failures)) => {
                for failure in source_failures {
                    failures.push(format!("{source_path}: {failure}"));
                }
                for d in decls {
                    let id = format!("{relative}_{}_{}", d.name.to_lowercase(), d.ordinal);
                    if !(d.r > 0
                        && d.s > 0
                        && d.labels > 0
                        && d.r <= 256
                        && d.s <= 4096
                        && d.labels <= 8192
                        && d.input < d.s
                        && d.output < d.s
                        && d.entry < d.labels)
                    {
                        failures.push(format!(
                            "{source_path}:{}: unsupported machine dimensions",
                            d.name
                        ));
                        continue;
                    }
                    let e = Extracted {
                        id,
                        file: source_path.clone(),
                        blob: blob.clone(),
                        r: d.r,
                        s: d.s,
                        labels: d.labels,
                        entry: d.entry,
                        input: d.input,
                        output: d.output,
                        table: d.body.join("\n"),
                    };
                    // Reject erroneous jump/port indices using the existing Rust generator's parser.
                    if let Err(err) = lean_table_codegen::generate(
                        &table(&e),
                        lean_table_codegen::TableKind::Catalog {
                            name: &e.id,
                            blob: &e.blob,
                            abi: (e.r, e.s, e.labels, e.entry, e.input, e.output),
                        },
                        8192,
                    ) {
                        failures.push(format!("{}:{}: {err}", e.file, d.name));
                        continue;
                    }
                    // Table bytes stored as instruction rows only until final assembly.
                    entries.push(e);
                }
            }
            Err(err) => failures.push(format!("{source_path}: {err}")),
        }
    }
    if entries.is_empty() {
        return Err("no finite literal source tables found".into());
    }
    Ok((entries, failures))
}
fn legacy(e: &Extracted) -> Option<(&'static str, &'static str)> {
    match (e.file.as_str(), e.id.as_str()) {
        (
            "lean/OAI/Algorithms/SubexponentialSAT/BinaryPrograms.lean",
            "binaryprograms_program_0",
        ) => Some(("binary-add", "ab8a858c2466aa3879087f825802aa76c7aa768f")),
        (
            "lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProgram.lean",
            "sqrtlogspace_queryprogram_parityprogram_0",
        ) => Some(("query-parity", "7a2535f7c479463a5f5ed8a30a33192aad1b063e")),
        (
            "lean/OAI/Algorithms/SubexponentialSAT/Subexp/TypeBitProgram.lean",
            "subexp_typebitprogram_program_0",
        ) => Some(("type-bit", "4e020c828e458b4420179da94c3451bea653a7b9")),
        _ => None,
    }
}
fn put(path: &Path, contents: &str, check: bool) -> Result<()> {
    if check {
        if fs::read_to_string(path).ok().as_deref() != Some(contents) {
            return Err(format!(
                "catalog differs from pinned original source: {}",
                path.display()
            ));
        }
    } else {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
        fs::write(path, contents).map_err(|e| e.to_string())?;
    }
    Ok(())
}
fn run() -> Result<()> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let get = |key: &str| -> Result<String> {
        let i = args
            .iter()
            .position(|s| s == key)
            .ok_or_else(|| format!("missing {key}"))?;
        args.get(i + 1)
            .cloned()
            .ok_or_else(|| format!("missing value for {key}"))
    };
    let root = PathBuf::from(get("--upstream")?);
    let output = PathBuf::from(get("--output-dir")?);
    let check = args.iter().any(|s| s == "--check");
    let legacy_mode = args.iter().any(|s| s == "--legacy");
    let (entries, failures) = extract(&root)?;
    if legacy_mode {
        let mut found = BTreeSet::new();
        for e in entries.iter() {
            let Some((name, pin)) = legacy(e) else {
                continue;
            };
            if e.blob != pin {
                return Err(format!("{name}: source Git blob mismatch"));
            }
            let mut other = e.clone();
            other.id = name.into();
            let source = table(&other);
            put(&output.join(format!("{name}.table")), &source, check)?;
            found.insert(name);
            println!("{name} {} {}", sha256(source.as_bytes())?, source.len());
        }
        if found.len() != 3 {
            return Err("three original literal tables not all found".into());
        }
    } else {
        let mut manifest =
            String::from("id\tfile\tgit_blob\tr\ts\tlabels\tentry\tinput\toutput\ttable_sha256\n");
        let mut bundle = format!(
            "ORIGINAL_LEAN_LITERAL_BUNDLE|1|{SOURCE}|{}\n",
            entries.len()
        );
        for (index, e) in entries.iter().enumerate() {
            let content = table(e);
            manifest.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                e.id,
                e.file,
                e.blob,
                e.r,
                e.s,
                e.labels,
                e.entry,
                e.input,
                e.output,
                sha256(content.as_bytes())?
            ));
            bundle.push_str(&content);
            if index + 1 < entries.len() {
                bundle.push('\n');
            }
        }
        bundle.push_str(&format!(
            "END_ORIGINAL_LEAN_LITERAL_BUNDLE|{}\n",
            entries.len()
        ));
        put(&output.join("all-literal.tsv"), &manifest, check)?;
        put(&output.join("all-literal.bundle"), &bundle, check)?;
        println!("compiled={} unsupported={}", entries.len(), failures.len());
        for problem in failures {
            println!("UNSUPPORTED\t{problem}");
        }
    }
    Ok(())
}
fn main() {
    if let Err(e) = run() {
        eprintln!("extract-lean-tables: {e}");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn instr_table_supports_literals_and_refuses_expressions() {
        let symbols = BTreeMap::new();
        assert_eq!(instruction(".set 0 true 1", &symbols).unwrap(), "set:0:1:1");
        assert_eq!(
            instruction(".bxor 0 1 2 3", &symbols).unwrap(),
            "xor:0:1:2:3"
        );
        assert!(instruction(".call f", &symbols).is_err());
        assert!(instruction(".pop x y z", &symbols).is_err());
    }
    #[test]
    fn extracts_all_three_source_syntaxes() {
        let sample = "def a : Program 2 1 2 where\n  inputStack := 0\n  outputStack := 0\n  entry := 0\n  code := ![.goto 1, .halt]\n\ndef b : Program 2 1 2 where\n  inputStack := 0\n  outputStack := 0\n  entry := 0\n  code q := match q.val with\n    | 0 => .goto 1\n    | _ => .halt\n\ndef c : Program 2 1 2 where\n  inputStack := 0\n  outputStack := 0\n  entry := 0\n  code := fun q => if q = 0 then .goto 1 else .halt\n";
        let (x, failures) = declarations(sample).unwrap();
        assert!(failures.is_empty());
        assert_eq!(x.len(), 3);
        assert_eq!(x[0].body, vec!["goto:1", "halt"]);
        assert_eq!(x[1].body, x[0].body);
        assert_eq!(x[2].body, x[0].body);
        assert_eq!([x[0].ordinal, x[1].ordinal, x[2].ordinal], [0, 1, 2]);
    }
    #[test]
    fn refuses_missing_labels_and_nonliteral_controllers() {
        let sym = BTreeMap::new();
        assert!(parse_code(&["code := ![.goto 1]".into()], 2, &sym).is_err());
        assert!(
            parse_code(
                &[
                    "code q := match q.val with".into(),
                    "  | 0 => .goto 1".into()
                ],
                2,
                &sym
            )
            .is_err()
        );
        assert!(
            parse_code(
                &["code := fun q => if q = 1 then .goto 0 else .halt".into()],
                2,
                &sym
            )
            .is_err()
        );
    }
}
