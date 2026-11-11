use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_bootstrap::{
    bootstrap_node_command, bootstrap_program, count_rows_command, initialize_address_command,
    initialize_cache_command, retain_cache_command,
};

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, i: usize, bits: &[bool]) {
    d.stacks[i] = bits.iter().copied().collect();
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, i: usize) -> Vec<bool> {
    d.stacks[i].iter().copied().collect()
}
fn input() -> Config<16, 768> {
    let mut d = bootstrap_program().unwrap().initial([]);
    put(&mut d, 130, &[true, true, true]);
    put(&mut d, 307, &[true, true]);
    put(&mut d, 136, &[true, false, true, false, true, false, false]);
    put(&mut d, 139, &[true, true]);
    put(&mut d, 138, &[true, true, true]);
    put(&mut d, 140, &[true; 13]);
    put(&mut d, 710, &[false, true]);
    put(&mut d, 711, &[true]);
    put(&mut d, 712, &[false]);
    put(&mut d, 660, &[false, true]);
    put(&mut d, 665, &[true, false]);
    put(&mut d, 659, &[true]);
    for i in 340..364 {
        put(&mut d, i, &[true, false]);
    }
    d
}
fn run<const R: usize, const S: usize>(
    program: &lean_eth_reference::bit_program::Program<R, S>,
    d: &mut Config<R, S>,
) -> u64 {
    program
        .run(
            d,
            RunLimits {
                max_steps: 30_000_000,
                max_stack_bits: 100_000,
            },
        )
        .unwrap()
        .instructions
}
#[test]
fn integrated_bootstrap_materializes_and_retains_real_coefficients() {
    let p = bootstrap_program().unwrap();
    assert_eq!((p.input_stack(), p.output_stack()), (307, 647));
    let mut d = input();
    let initial = d.clone();
    assert!(run(&p, &mut d) > 1000);
    let positive = get(&d, 640);
    assert_eq!(positive.len(), 39);
    let val = |i: usize| -> u64 {
        (0..13)
            .filter(|&bit| positive[i * 13 + bit])
            .fold(0u64, |n, bit| n | (1u64 << bit))
    };
    assert_eq!([val(0), val(1), val(2)], [1, 5, 17]);
    assert_eq!(get(&d, 641), vec![false; 39]);
    assert_eq!(get(&d, 642), vec![false, false, true]);
    assert_eq!(get(&d, 643), vec![true; 13]);
    assert_eq!(get(&d, 647), vec![true; 3]);
    assert_eq!(get(&d, 648), vec![true; 3]);
    assert_eq!(get(&d, 649), vec![true; 6]);
    for (src, dst) in [(640, 710), (641, 711), (642, 712)] {
        assert_eq!(get(&d, dst), [get(&d, src), get(&initial, dst)].concat());
    }
    for port in [130, 136, 138, 139, 140, 307, 660, 665] {
        assert_eq!(d.stacks[port], initial.stacks[port]);
    }
    for port in 340..364 {
        assert!(d.stacks[port].is_empty(), "{port}");
    }
    assert!(d.stacks[659].is_empty());
}
#[test]
fn composed_program_and_explicit_stage_sequence_agree_on_full_machine_state() {
    let whole = bootstrap_program().unwrap();
    let stages = [
        initialize_address_command()
            .unwrap()
            .compiled(307, 647)
            .unwrap(),
        count_rows_command().unwrap().compiled(307, 647).unwrap(),
        initialize_cache_command()
            .unwrap()
            .compiled(307, 647)
            .unwrap(),
        retain_cache_command().unwrap().compiled(307, 647).unwrap(),
    ];
    let mut a = input();
    let mut b = a.clone();
    run(&whole, &mut a);
    for p in &stages {
        b.pc = Some(p.entry());
        run(p, &mut b);
    }
    assert_eq!(a.regs, b.regs);
    assert_eq!(a.stacks, b.stacks);
}
#[test]
fn wide_node_callback_equals_local_bootstrap_and_preserves_unmapped_ports() {
    let local = bootstrap_program().unwrap();
    let wide = bootstrap_node_command()
        .unwrap()
        .compiled(435, 775)
        .unwrap();
    let mut low = input();
    let mut outer = wide.initial([]);
    for i in 0..768 {
        outer.stacks[i + 128] = low.stacks[i].clone();
    }
    outer.regs[24..40].copy_from_slice(&low.regs);
    outer.regs[3] = true;
    put(&mut outer, 127, &[true, false]);
    run(&local, &mut low);
    run(&wide, &mut outer);
    assert_eq!(&outer.regs[24..40], &low.regs);
    assert!(outer.regs[3]);
    assert_eq!(get(&outer, 127), vec![true, false]);
    for i in 0..768 {
        assert_eq!(outer.stacks[i + 128], low.stacks[i], "{i}");
    }
}
#[test]
fn bootstrap_refuses_to_report_success_on_step_exhaustion() {
    let p = bootstrap_program().unwrap();
    let mut d = input();
    assert!(matches!(
        p.run(
            &mut d,
            RunLimits {
                max_steps: 32,
                max_stack_bits: 100_000
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert!(d.pc.is_some());
}
