use std::{env, path::PathBuf, process::Command};
fn main() {
    println!("cargo:rerun-if-changed=native/abi.c");
    println!("cargo:rerun-if-env-changed=LEAN_PREFIX");
    let prefix =
        env::var_os("LEAN_PREFIX").expect("LEAN_PREFIX must point to pinned Lean distribution");
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
}
