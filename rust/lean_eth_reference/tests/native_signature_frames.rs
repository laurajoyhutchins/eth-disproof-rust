//! Machine-level regression tests, independent of host tuple enumeration.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_signature_frames::*;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, i: usize, bits: &[bool]) {
    d.stacks[i] = bits.iter().copied().collect();
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, i: usize) -> Vec<bool> {
    d.stacks[i].iter().copied().collect()
}
fn exec<const R: usize, const S: usize>(p: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    let t = p.run(d, RunLimits { max_steps: 100_000, max_stack_bits: 100_000 }).unwrap();
    assert_eq!(d.pc, None);
    t.instructions
}
fn run(c: Cmd<40, 896>, d: &mut Config<40, 896>) {
    let p = c.compiled(836, 837).unwrap();
    d.pc = Some(p.entry());
    exec(&p, d);
}
fn frame(bits: &[bool]) -> Vec<bool> {
    let mut xs = Vec::new();
    for b in bits.iter().rev() {
        xs.extend([true, *b]);
    }
    xs.push(false);
    xs
}

#[test]
fn pinned_layout_and_invalid_lifts() {
    assert_eq!(TUPLE_STACKS, [836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]);
    assert_eq!(CONTROLLER_REGISTERS, [36, 37, 38, 39]);
    assert_eq!(CURRENT_HEAD_PORTS, [838, 839, 840, 841, 843, 844, 846, 847]);
    assert!(matches!(push_word_command(845, 845), Err(Error::Invalid(_))));
    assert!(matches!(pop_word_command(900, 845), Err(Error::Invalid(_))));
}
#[test]
fn writer_uses_exact_source_step_count_and_reversed_frame() {
    let p = push_frame_program().unwrap();
    assert_eq!(p.code().len(), 8);
    for n in 0..30 {
        let w: Vec<_> = (0..n).map(|i| i % 3 != 1).collect();
        let mut d = p.initial(w.clone());
        put(&mut d, 1, &[false, true]);
        assert_eq!(exec(&p, &mut d), 5 * n as u64 + 5);
        assert!(get(&d, 0).is_empty());
        let mut expected = frame(&w);
        expected.extend([false, true]);
        assert_eq!(get(&d, 1), expected);
    }
}
#[test]
fn nested_cursor_frames_restore_exactly_including_empty_words() {
    for candidate in [vec![], vec![false], vec![true, false, true]] {
        for remaining in [vec![], vec![true], vec![false, true, true]] {
            let mut d = Cmd::<40, 896>::Skip.compiled(836, 838).unwrap().initial([]);
            let frames = [false, true, false, false];
            put(&mut d, 836, &frames);
            put(&mut d, 838, &candidate);
            put(&mut d, 843, &remaining);
            put(&mut d, 895, &[true, false]);
            run(save_cursor_command().unwrap(), &mut d);
            let mut expected = frame(&remaining);
            expected.extend(frame(&candidate));
            expected.extend(frames);
            assert_eq!(get(&d, 836), expected);
            assert!(get(&d, 838).is_empty() && get(&d, 843).is_empty());
            run(restore_cursor_command().unwrap(), &mut d);
            assert_eq!(get(&d, 836), frames);
            assert_eq!(get(&d, 838), candidate);
            assert_eq!(get(&d, 843), remaining);
            assert_eq!(get(&d, 895), [true, false]);
        }
    }
}
#[test]
fn suspend_and_resume_consume_one_real_frame() {
    for word in [vec![], vec![true], vec![false, true, false]] {
        let mut d = Cmd::<40, 896>::Skip.compiled(836, 840).unwrap().initial([]);
        put(&mut d, 840, &word);
        put(&mut d, 836, &[false]);
        run(suspend_command().unwrap(), &mut d);
        let mut expected = frame(&word);
        expected.push(false);
        assert_eq!(get(&d, 836), expected);
        run(resume_command().unwrap(), &mut d);
        assert_eq!(get(&d, 840), word);
        assert_eq!(get(&d, 836), [false]);
    }
}
#[test]
fn representative_record_drop_retains_original_candidate() {
    for candidate in [vec![], vec![true], vec![false, true, true]] {
        let mut d = Cmd::<40, 896>::Skip.compiled(837, 840).unwrap().initial([]);
        put(&mut d, 837, &[false]);
        put(&mut d, 838, &candidate);
        run(record_representative_command().unwrap(), &mut d);
        let mut expected = frame(&candidate);
        expected.push(false);
        assert_eq!(get(&d, 837), expected);
        assert_eq!(get(&d, 838), candidate);
        assert!(get(&d, 840).is_empty());
        run(drop_representative_command().unwrap(), &mut d);
        assert_eq!(get(&d, 837), [false]);
        assert!(get(&d, 840).is_empty());
    }
}
#[test]
fn level_roundtrip_and_empty_frame_presence() {
    for heads in 1..=5 {
        let mut d = Cmd::<40, 896>::Skip.compiled(842, 845).unwrap().initial([]);
        put(&mut d, 842, &vec![true; heads]);
        put(&mut d, 845, &[true, true]);
        run(descend_level_command(), &mut d);
        assert_eq!(get(&d, 842), vec![true; heads - 1]);
        assert_eq!(get(&d, 845), [true, true, true]);
        assert_eq!(d.regs[37], heads == 1);
        run(ascend_level_command(), &mut d);
        assert_eq!(get(&d, 842), vec![true; heads]);
        assert_eq!(get(&d, 845), [true, true]);
        assert!(!d.regs[37]);
        put(&mut d, 836, &[false]);
        run(test_parent_command(), &mut d);
        assert!(d.regs[36]);
        put(&mut d, 836, &[]);
        run(test_parent_command(), &mut d);
        assert!(!d.regs[36]);
    }
}
#[test]
fn fresh_latch_and_head_cleanup_preserve_protected_stacks() {
    let mut d = Cmd::<40, 896>::Skip.compiled(362, 362).unwrap().initial([]);
    put(&mut d, 362, &[true, false, true, true]);
    put(&mut d, 836, &[false]);
    put(&mut d, 895, &[true, false]);
    run(initialize_fresh_command().unwrap(), &mut d);
    assert_eq!(get(&d, 362), [false]);
    for i in CURRENT_HEAD_PORTS {
        put(&mut d, i, &[true, false]);
    }
    run(leave_head_command().unwrap(), &mut d);
    for i in CURRENT_HEAD_PORTS {
        assert!(get(&d, i).is_empty());
    }
    assert_eq!(get(&d, 836), [false]);
    assert_eq!(get(&d, 895), [true, false]);
}
#[test]
fn long_frame_fails_closed_on_step_limit() {
    let p = save_cursor_command().unwrap().compiled(836, 838).unwrap();
    let mut d = p.initial([]);
    put(&mut d, 838, &[true; 50]);
    assert!(matches!(p.run(&mut d, RunLimits { max_steps: 3, max_stack_bits: 100_000 }), Err(Error::Capacity(_))));
}
