use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_loader_frames::{
    export_matrix_command, export_matrix_leaf_command, export_matrix_program,
    import_address_from_command, import_address_from_program, import_address_leaf_command,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, p: usize, v: &[bool]) {
    d.stacks[p] = VecDeque::from(v.to_vec());
}
fn read<const R: usize, const S: usize>(d: &Config<R, S>, p: usize) -> Vec<bool> {
    d.stacks[p].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    p.run(d, RunLimits::default()).unwrap().instructions
}
#[test]
fn paid_address_import_preserves_alternate_sources_and_frames() {
    for src in [845, 700, 895] {
        let p = import_address_from_program(src).unwrap();
        assert_eq!(
            p.code().len(),
            import_address_from_command(src).unwrap().size().unwrap() + 1
        );
        for n in 0..=7 {
            let word = (0..n).map(|i| i % 2 == 1).collect::<Vec<_>>();
            let mut d = p.initial(word.clone());
            put(&mut d, 649, &[true, true, false]);
            put(&mut d, 659, &[false, true]);
            put(&mut d, 846, &[true]);
            put(&mut d, 847, &[true, false]);
            put(&mut d, 300, &[true, false, true]);
            d.regs[3] = true;
            d.regs[15] = true;
            let expected = (2 * 3 + 3) + (2 * 2 + 3) + (2 + 3) + (2 * 2 + 3) + (7 * n + 5) + 1;
            assert_eq!(run(&p, &mut d), expected as u64);
            assert_eq!(read(&d, 649), word);
            assert_eq!(read(&d, src), word);
            for port in [659, 846, 847] {
                assert!(d.stacks[port].is_empty());
            }
            assert_eq!(read(&d, 300), vec![true, false, true]);
            assert!(d.regs[3] && d.regs[15]);
            assert_eq!(d.pc, None);
        }
    }
    for src in [649, 659, 846, 847] {
        assert!(matches!(
            import_address_from_command(src),
            Err(Error::Invalid(_))
        ));
    }
    assert!(import_address_from_command(896).is_err());
}
#[test]
fn paid_matrix_export_prepends_without_dropping_dirty_tails() {
    let p = export_matrix_program().unwrap();
    assert_eq!(
        p.code().len(),
        export_matrix_command().unwrap().size().unwrap() + 1
    );
    for n in 0..=9 {
        let mut d = p.initial((0..n).map(|i| i % 2 == 0));
        let src = read(&d, 668);
        let old_dst = vec![false, true, false];
        put(&mut d, 847, &old_dst);
        put(&mut d, 659, &[false, true]);
        put(&mut d, 669, &[true, true, true, true]);
        put(&mut d, 846, &[true, false]);
        put(&mut d, 890, &[true, true]);
        d.regs[12] = true;
        let steps = (2 * 2 + 3) + (7 * n + 5) + (2 * n + 3) + (2 * 4 + 3) + (2 * 2 + 3) + 1;
        assert_eq!(run(&p, &mut d), steps as u64);
        assert_eq!(read(&d, 847), [src, old_dst.clone()].concat());
        for port in [659, 668, 669, 846] {
            assert!(d.stacks[port].is_empty());
        }
        assert_eq!(read(&d, 890), vec![true, true]);
        assert!(d.regs[12]);
    }
}
#[test]
fn shell_without_local_computation_does_not_pretend_to_compute_matrix() {
    let source = 845;
    let p = Cmd::seq(
        import_address_from_command(source).unwrap(),
        export_matrix_command().unwrap(),
    )
    .compiled(source, 847)
    .unwrap();
    let mut d = p.initial([true, false, true]);
    put(&mut d, 668, &[true, true, false]); // diagnostic pre-populated matrix
    put(&mut d, 847, &[true, true, true]);
    run(&p, &mut d);
    assert_eq!(read(&d, 649), vec![true, false, true]);
    assert_eq!(read(&d, 847), vec![true, true, false]);
    assert!(read(&d, 668).is_empty());
}
#[test]
fn full_leaf_register_lift_keeps_global_controls_untouched() {
    let import = import_address_leaf_command(845).unwrap();
    let export = export_matrix_leaf_command().unwrap();
    let p = Cmd::seq(import, export).compiled(845, 847).unwrap();
    let mut d = p.initial([true, false, true, true]);
    put(&mut d, 668, &[false, true, false]);
    put(&mut d, 847, &[true]);
    d.regs[0] = true;
    d.regs[19] = true;
    d.regs[23] = true;
    let regs = d.regs;
    run(&p, &mut d);
    assert_eq!(d.regs[..24], regs[..24]);
    assert_eq!(read(&d, 649), vec![true, false, true, true]);
    assert_eq!(read(&d, 847), vec![false, true, false]);
    assert!(d.stacks[659].is_empty());
}
#[test]
fn incomplete_execution_must_not_be_reported_as_halt() {
    let p = export_matrix_program().unwrap();
    let mut d = p.initial([true; 35]);
    let e = p.run(
        &mut d,
        RunLimits {
            max_steps: 8,
            max_stack_bits: 100000,
        },
    );
    assert!(matches!(e, Err(Error::Capacity(_))));
    assert!(d.pc.is_some());
}
