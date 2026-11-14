use std::{env, fmt::Write as _, fs, path::PathBuf, process::Command};
fn main() {
    println!("cargo:rerun-if-changed=native/abi.c");
    println!("cargo:rerun-if-changed=ir-coverage-classification.tsv");
    println!("cargo:rerun-if-env-changed=LEAN_PREFIX");
    let prefix =
        env::var_os("LEAN_PREFIX").expect("LEAN_PREFIX must point to pinned Lean distribution");
    let lean = PathBuf::from(&prefix).join("bin/lean");
    let version = Command::new(&lean)
        .arg("--version")
        .output()
        .expect("run exact Lean 4.34.1 compiler");
    let version_text = String::from_utf8_lossy(&version.stdout);
    assert!(
        version.status.success()
            && version_text.contains("version 4.34.1,")
            && version_text.contains("5045d0056413266e57c625dcd7c365b10e377c52"),
        "native ABI requires Lean 4.34.1 commit 5045d005: found {version_text}"
    );
    assert!(
        env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("x86_64")
            && env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("linux"),
        "native backend v0.1 has been audited only on Linux x86-64"
    );
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));
    let obj = out.join("abi.o");
    let archive = out.join("libnative_lean_abi.a");
    let cc = env::var_os("CC").unwrap_or("cc".into());
    let status = Command::new(cc)
        .arg("-std=c11")
        .arg("-fPIC")
        .arg("-I")
        .arg(PathBuf::from(prefix).join("include"))
        .arg("-c")
        .arg("native/abi.c")
        .arg("-o")
        .arg(&obj)
        .status()
        .expect("compile Lean C ABI accessors");
    assert!(status.success(), "Lean C ABI shim failed");
    let status = Command::new("ar")
        .arg("crs")
        .arg(&archive)
        .arg(&obj)
        .status()
        .expect("archive Lean ABI accessors");
    assert!(status.success(), "Lean ABI archiving failed");
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=native_lean_abi");
    // Consume the same reviewed constructor classifications as the Lean
    // source-derived coverage gate. Production IR decoding refuses anything
    // not classified implemented_bounded, even if a future match arm is added.
    let mut tags = String::from("const SUPPORTED_IR_TAGS: &[(&str, usize)] = &[\n");
    let contract = fs::read_to_string("ir-coverage-classification.tsv")
        .expect("pinned IR constructor coverage classification is required");
    let mut count = 0;
    for line in contract
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
    {
        let cells: Vec<_> = line.split('\t').collect();
        assert_eq!(cells.len(), 5, "malformed pinned IR coverage row: {line}");
        let full_name = cells[0];
        let family = full_name
            .rsplit_once('.')
            .and_then(|(prefix, _)| prefix.rsplit_once('.').map(|(_, name)| name))
            .expect("fully qualified Lean IR constructor");
        let tag: usize = cells[1].parse().expect("numeric Lean IR tag");
        match cells[2] {
            "implemented_bounded" => {
                assert!(
                    matches!(
                        family,
                        "Decl" | "IRType" | "Arg" | "LitVal" | "Expr" | "Alt" | "FnBody"
                    ),
                    "unrecognized IR family {family}"
                );
                writeln!(&mut tags, "    (\"{family}\", {tag}),").unwrap();
                count += 1;
            }
            "explicitly_unsupported" => (),
            other => panic!("invalid IR coverage classification: {other}"),
        }
    }
    assert!(count > 0, "IR registry has no supported constructors");
    tags.push_str("];\n");
    fs::write(out.join("ir_coverage_tags.rs"), tags)
        .expect("write coverage-gated IR constructor table");
}
