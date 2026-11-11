//! Compiles every exactly recognized fixed literal finite program from the
//! pinned upstream source. Unsupported non-literal code is not lowered.
#[allow(dead_code)]
mod catalog {
    include!(concat!(env!("OUT_DIR"), "/original_catalog.rs"));
}

#[test]
fn original_catalog_source_programs_are_compiled() {
    assert_eq!(catalog::source_0::LABELS, 13);
    // Last table corresponds to the final lexically sorted original file.
    assert_eq!(catalog::source_58::LABELS, 13);
}
