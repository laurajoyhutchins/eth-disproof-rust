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
    let input = include_str!("tools/fixtures/tiny.table");
    let generated =
        lean_table_codegen::generate(input, lean_table_codegen::TableKind::Fixture, 1024)
            .expect("synthetic instruction table must validate");
    let path =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo OUT_DIR")).join("compiled_fixture.rs");
    fs::write(path, generated).expect("write generated Rust fixture");
}
