use std::env;
use std::fs;
use std::path::Path;
use std::process;
use std::time::Instant;

fn compile(input: &Path, output: &Path, namespace: &str) -> Result<(), String> {
    let content = fs::read_to_string(input).map_err(|e| format!("{}: {e}", input.display()))?;
    let ast = structural_latex::parse_article(&content).map_err(|e| e.to_string())?;
    let generated = structural_latex::to_lean(&ast, namespace).map_err(|e| e.to_string())?;
    let parent = output.parent().ok_or("missing output directory")?;
    fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    let temp = output.with_extension("lean.tmp");
    fs::write(&temp, generated).map_err(|e| e.to_string())?;
    fs::rename(&temp, output).map_err(|e| e.to_string())
}
fn run_batch(from: &Path, to: &Path) -> Result<(), String> {
    let mut files = fs::read_dir(from)
        .map_err(|e| e.to_string())?
        .map(|e| e.map(|x| x.path()).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    files.retain(|x| x.extension().is_some_and(|e| e == "tex"));
    files.sort();
    if files.is_empty() {
        return Err("empty .tex corpus".to_owned());
    }
    let start = Instant::now();
    for file in &files {
        let stem = file
            .file_stem()
            .and_then(|s| s.to_str())
            .ok_or("invalid source filename")?;
        let target = to.join(format!("Structural{stem}.lean"));
        compile(file, &target, &format!("Structural{stem}"))?;
        println!("compiled\t{}\t{}", file.display(), target.display());
    }
    eprintln!(
        "compiled {} article(s) in {} ms",
        files.len(),
        start.elapsed().as_millis()
    );
    Ok(())
}
fn main() {
    let args = env::args().collect::<Vec<_>>();
    let result = match args.as_slice() {
        [_, flag, from, to] if flag == "--batch" => {
            run_batch(Path::new(from), Path::new(to))
        }
        [_, input, output, namespace] => compile(
            Path::new(input),
            Path::new(output),
            namespace,
        ),
        _ => Err("usage: structural-latex SOURCE.tex OUT.lean NAMESPACE\n       structural-latex --batch SOURCE_DIR OUTPUT_DIR".to_owned()),
    };
    if let Err(e) = result {
        eprintln!("{e}");
        process::exit(1)
    }
}
