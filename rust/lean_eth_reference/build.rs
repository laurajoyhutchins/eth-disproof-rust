// The tiny fixture is *synthetic*. It exercises compilation and Rust-machine
// equivalence without requiring the still-unavailable imported Lean runtime.
#[path = "tools/lean_table_codegen.rs"]
mod lean_table_codegen;

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=tools/lean_table_codegen.rs");
    println!("cargo:rerun-if-changed=tools/fixtures/tiny.table");
    for (name, kind) in [
        (
            "binary-add",
            lean_table_codegen::TableKind::OriginalBinaryAdd,
        ),
        (
            "query-parity",
            lean_table_codegen::TableKind::OriginalQueryParity,
        ),
        ("type-bit", lean_table_codegen::TableKind::OriginalTypeBit),
    ] {
        let input_path = format!("tools/fixtures/original/{name}.table");
        println!("cargo:rerun-if-changed={input_path}");
        let source = fs::read_to_string(input_path).expect("pinned source table file");
        let generated = lean_table_codegen::generate(&source, kind, 1024)
            .expect("pinned source machine must validate");
        let path = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo OUT_DIR"))
            .join(format!("original_{name}.rs"));
        fs::write(path, generated).expect("write generated original Rust");
    }
    println!("cargo:rerun-if-changed=tools/fixtures/original/all-literal.tsv");
    println!("cargo:rerun-if-changed=tools/fixtures/original/all-literal.bundle");
    let catalog = include_str!("tools/fixtures/original/all-literal.tsv");
    let bundle = include_str!("tools/fixtures/original/all-literal.bundle");
    let mut records = bundle.lines();
    let mut manifest = catalog.lines();
    assert!(manifest.next().unwrap().starts_with("id\tfile\tgit_blob\t"));
    let expected_count = manifest.clone().count();
    assert_eq!(records.next(), Some(format!(
        "ORIGINAL_LEAN_LITERAL_BUNDLE|1|4eaee87548250b2682affda7d05d947c05554bae|{expected_count}"
    ).as_str()));
    let mut all_rust = String::new();
    all_rust.push_str(&format!(
        "// @generated from {expected_count} original pinned Lean program declarations.\n"
    ));
    for (i, record) in manifest.enumerate() {
        let fields: Vec<_> = record.split('\t').collect();
        assert_eq!(fields.len(), 10, "catalog schema");
        let name = fields[0];
        let blob = fields[2];
        let nums: Vec<usize> = fields[3..9].iter().map(|s| s.parse().unwrap()).collect();
        let abi = (nums[0], nums[1], nums[2], nums[3], nums[4], nums[5]);
        let pin = records.next().expect("source PIN");
        assert_eq!(
            pin,
            format!("PIN|{name}|4eaee87548250b2682affda7d05d947c05554bae|{blob}")
        );
        let header = records.next().expect("source program header");
        assert_eq!(
            header,
            format!(
                "PROGRAM|{name}|{}|{}|{}|{}|{}|{}",
                abi.0, abi.1, abi.2, abi.3, abi.4, abi.5
            )
        );
        let mut table = format!("{pin}\n{header}\n");
        for _ in 0..abi.2 {
            table.push_str(records.next().expect("source CODE record"));
            table.push('\n');
        }
        let end = records.next().expect("source END record");
        assert_eq!(end, format!("END|{name}|{}", abi.2));
        table.push_str(end);
        table.push('\n');
        let generated = lean_table_codegen::generate(
            &table,
            lean_table_codegen::TableKind::Catalog { name, blob, abi },
            8192,
        )
        .expect("pinned source catalog table");
        all_rust.push_str(&format!("pub mod source_{i} {{\n"));
        all_rust.push_str(&generated);
        all_rust.push_str("}\n");
        if i + 1 != expected_count {
            assert_eq!(records.next(), Some(""), "catalog table separator");
        }
    }
    assert_eq!(
        records.next(),
        Some(format!("END_ORIGINAL_LEAN_LITERAL_BUNDLE|{expected_count}").as_str())
    );
    assert_eq!(records.next(), None, "catalog bundle trailing content");
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo OUT_DIR"));
    fs::write(out_dir.join("original_catalog.rs"), all_rust).expect("write all source programs");
    // Exercise code generation beyond a single Rust match, with cross-chunk
    // jumps and an invalid-PC refusal. Test data remains explicitly synthetic.
    let labels = 640;
    let mut large = format!("PIN|fixture|synthetic\nPROGRAM|fixture|4|3|{labels}|0|0|2\n");
    for i in 0..labels {
        let instruction = match i {
            0 => "set:0:1:1".to_string(),
            1 => "push:0:0:2".to_string(),
            2 => "peek:0:1:2:3".to_string(),
            3 => "pop:0:1:2:4".to_string(),
            4 => "branch:2:5:638".to_string(),
            638 => "pop:1:0:2:639".to_string(),
            639 => "halt".to_string(),
            _ => format!("goto:{}", i + 1),
        };
        large.push_str(&format!("CODE|fixture|{i}|{instruction}\n"));
    }
    large.push_str(&format!("END|fixture|{labels}\n"));
    let generated_large =
        lean_table_codegen::generate(&large, lean_table_codegen::TableKind::Fixture, 1024)
            .expect("bounded 640-label code generation");
    let chunked_path =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo OUT_DIR")).join("chunked_fixture.rs");
    fs::write(chunked_path, generated_large).expect("write chunked generated Rust");

    let input = include_str!("tools/fixtures/tiny.table");
    let generated =
        lean_table_codegen::generate(input, lean_table_codegen::TableKind::Fixture, 1024)
            .expect("synthetic instruction table must validate");
    let path =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo OUT_DIR")).join("compiled_fixture.rs");
    fs::write(path, generated).expect("write generated Rust fixture");
}
