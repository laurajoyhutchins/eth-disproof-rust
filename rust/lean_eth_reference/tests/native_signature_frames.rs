//! Independent state assertions for the source's physical tuple frame protocol.
//! Tests run only actual bit instructions, not a Rust tuple enumerator.

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_signature_frames::{
    CONTROLLER_REGISTERS, CURRENT_HEAD_PORTS, TUPLE_STACKS, ascend_level_command,
    descend_level_command, drop_representative_command, initialize_fresh_command,
    leave_head_command, pop_word_command, push_frame_program, push_word_command,
    record_representative_command, restore_cursor_command, resume_command, save_cursor_command,
    suspend_command, test_parent_command,
};

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, stack: usize, value: &[bool]) {
    d.stacks[stack] = value.iter().copied().collect();
}
fn got<const R: usize, const S: usize>(d: &Config<R, S>, stack: usize) -> Vec<bool> {
    d.stacks[stack].iter().copied().collect()
}
fn execute<const R: usize, const S: usize>(p: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    let stats = p
        .run(
            d,
            RunLimits {
                max_steps: 1_000_000,
                max_stack_bits: 100_000,
            },
        )
        .unwrap();
    assert!(d.pc.is_none());
    stats.instructions
}
fn run(c: Cmd<40, 896>, d: &mut Config<40, 896>) -> u64 {
    let p = c.compiled(836, 837).unwrap();
    d.pc = Some(p.entry());
    execute(&p, d)
}
fn encoded_reversed(word: &[bool]) -> Vec<bool> {
    let mut output = Vec::with_capacity(2 * word.len() + 1);
    for &bit in word.iter().rev() {
        output.extend([true, bit]);
    }
    output.push(false);
    output
}

#[test]
fn pinned_tuple_ports_and_push_frame_machine_labels() {
    assert_eq!(
        TUPLE_STACKS,
        [836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]
    );
    assert_eq!(CONTROLLER_REGISTERS, [36, 37, 38, 39]);
    assert_eq!(CURRENT_HEAD_PORTS, [838, 839, 840, 841, 843, 844, 846, 847]);
    let p = push_frame_program().unwrap();
    assert_eq!(p.code().len(), 8);
    assert_eq!(p.input_stack(), 0);
    assert_eq!(p.output_stack(), 1);
    assert!(matches!(
        push_word_command(845, 845),
        Err(Error::Invalid(_))
    ));
    assert!(matches!(pop_word_command(900, 845), Err(Error::Invalid(_))));
    assert!(matches!(
        push_word_command(845, 900),
        Err(Error::Invalid(_))
    ));
}

#[test]
fn eight_label_frame_machine_exact_steps_and_framing() {
    let p = push_frame_program().unwrap();
    for n in 0..=25 {
        let word: Vec<_> = (0..n).map(|i| i % 3 != 1).collect();
        let suffix = vec![false, true, false, false, true];
        let mut d = p.initial(word.clone());
        put(&mut d, 1, &suffix);
        let steps = execute(&p, &mut d);
        assert_eq!(steps, 5 * n as u64 + 5, "input length {n}");
        assert_eq!(got(&d, 0), Vec::<bool>::new());
        let mut expected = encoded_reversed(&word);
        expected.extend(suffix);
        assert_eq!(got(&d, 1), expected);
        assert!(!d.regs[0]);
        assert!(!d.regs[1]);
    }
}

#[test]
fn generic_push_pop_roundtrip_including_empty_and_nonempty_delimiters() {
    for word in [
        vec![],
        vec![true],
        vec![false, true, false, true],
        vec![true; 32],
    ] {
        let mut d = Cmd::<40, 896>::Skip.compiled(500, 501).unwrap().initial([]);
        let suffix = vec![false, true, true, false];
        put(&mut d, 660, &word);
        put(&mut d, 661, &suffix);
        put(&mut d, 895, &[true, false, true]);
        run(push_word_command(660, 661).unwrap(), &mut d);
        let mut expected = encoded_reversed(&word);
        expected.extend(suffix.clone());
        assert_eq!(got(&d, 661), expected);
        assert!(got(&d, 660).is_empty());
        run(pop_word_command(661, 660).unwrap(), &mut d);
        assert_eq!(got(&d, 660), word);
        assert_eq!(got(&d, 661), suffix);
        assert_eq!(got(&d, 895), [true, false, true]);
    }
}

#[test]
fn save_restore_cursor_is_a_physical_stack_roundtrip() {
    for candidate in [vec![], vec![false], vec![true, false, true]] {
        for remaining in [vec![], vec![true], vec![false, true, true, false]] {
            let mut d = Cmd::<40, 896>::Skip.compiled(836, 838).unwrap().initial([]);
            let frames = vec![false, true, true, false, false];
            put(&mut d, 836, &frames);
            put(&mut d, 838, &candidate);
            put(&mut d, 843, &remaining);
            put(&mut d, 839, &[false, false, true]);
            put(&mut d, 895, &[true, false]);
            run(save_cursor_command().unwrap(), &mut d);
            let mut expected = encoded_reversed(&remaining);
            expected.extend(encoded_reversed(&candidate));
            expected.extend(frames.clone());
            assert_eq!(got(&d, 836), expected);
            assert!(got(&d, 838).is_empty());
            assert!(got(&d, 843).is_empty());
            run(restore_cursor_command().unwrap(), &mut d);
            assert_eq!(got(&d, 836), frames);
            assert_eq!(got(&d, 838), candidate);
            assert_eq!(got(&d, 843), remaining);
            assert_eq!(got(&d, 839), [false, false, true]);
            assert_eq!(got(&d, 895), [true, false]);
        }
    }
}

#[test]
fn source_suspend_resume_frames_include_empty_payload() {
    for w in [vec![], vec![false], vec![true, false, false, true]] {
        let mut d = Cmd::<40, 896>::Skip.compiled(836, 840).unwrap().initial([]);
        put(&mut d, 840, &w);
        put(&mut d, 836, &[false]);
        run(suspend_command().unwrap(), &mut d);
        let mut expected = encoded_reversed(&w);
        expected.push(false);
        assert_eq!(got(&d, 836), expected);
        run(resume_command().unwrap(), &mut d);
        assert_eq!(got(&d, 840), w);
        assert_eq!(got(&d, 836), [false]);
    }
}

#[test]
fn representative_record_and_drop_preserve_candidate_and_prior_frame() {
    for candidate in [vec![], vec![true], vec![false, true, true, false]] {
        let mut d = Cmd::<40, 896>::Skip.compiled(837, 840).unwrap().initial([]);
        let prior = vec![true, false, false];
        put(&mut d, 838, &candidate);
        put(&mut d, 837, &prior);
        put(&mut d, 847, &[true, false]);
        run(record_representative_command().unwrap(), &mut d);
        let mut expected = encoded_reversed(&candidate);
        expected.extend(prior.clone());
        assert_eq!(got(&d, 837), expected);
        assert!(got(&d, 840).is_empty());
        assert!(got(&d, 841).is_empty());
        assert_eq!(got(&d, 838), candidate);
        run(drop_representative_command().unwrap(), &mut d);
        assert_eq!(got(&d, 837), prior);
        assert!(got(&d, 840).is_empty());
        assert_eq!(got(&d, 847), [true, false]);
    }
}

#[test]
fn descend_and_ascend_update_unary_level_and_address() {
    for heads in 1..=5 {
        for addr in 0..=4 {
            let mut d = Cmd::<40, 896>::Skip.compiled(842, 845).unwrap().initial([]);
            put(&mut d, 842, &vec![true; heads]);
            put(&mut d, 845, &vec![true; addr]);
            put(&mut d, 895, &[false, true]);
            run(descend_level_command(), &mut d);
            assert_eq!(got(&d, 842), vec![true; heads - 1]);
            assert_eq!(got(&d, 845), vec![true; addr + 1]);
            assert_eq!(d.regs[37], heads == 1);
            run(ascend_level_command(), &mut d);
            assert_eq!(got(&d, 842), vec![true; heads]);
            assert_eq!(got(&d, 845), vec![true; addr]);
            assert!(!d.regs[37]);
            assert_eq!(got(&d, 895), [false, true]);
        }
    }
}

#[test]
fn root_presence_is_not_confused_with_first_bit_value() {
    for (frames, present) in [
        (vec![], false),
        (vec![false], true),
        (vec![false, true, false], true),
    ] {
        let mut d = Cmd::<40, 896>::Skip.compiled(836, 836).unwrap().initial([]);
        put(&mut d, 836, &frames);
        d.regs[36] = !present;
        run(test_parent_command(), &mut d);
        assert_eq!(d.regs[36], present);
        assert_eq!(got(&d, 836), frames);
    }
}

#[test]
fn initial_fresh_wipes_stale_predicate_latch_without_touching_frame() {
    let mut d = Cmd::<40, 896>::Skip.compiled(362, 362).unwrap().initial([]);
    put(&mut d, 362, &[true, false, true, true]);
    put(&mut d, 836, &[false]);
    let steps = run(initialize_fresh_command().unwrap(), &mut d);
    assert_eq!(steps, 2 * 4 + 5 + 1);
    assert_eq!(got(&d, 362), [false]);
    assert_eq!(got(&d, 836), [false]);
    assert!(!d.regs[0]);
}

#[test]
fn leave_head_clears_only_transient_ports_and_preserves_cursor_frame_and_budget() {
    let mut d = Cmd::<40, 896>::Skip.compiled(836, 836).unwrap().initial([]);
    for i in 836..848 {
        put(&mut d, i, &[true, false]);
    }
    put(&mut d, 895, &[false, false, true]);
    run(leave_head_command().unwrap(), &mut d);
    for i in 836..848 {
        if CURRENT_HEAD_PORTS.contains(&i) {
            assert!(got(&d, i).is_empty(), "should clear {i}");
        } else {
            assert_eq!(got(&d, i), [true, false], "should retain {i}");
        }
    }
    assert_eq!(got(&d, 895), [false, false, true]);
}

#[test]
fn unbounded_word_growth_is_never_silently_accepted() {
    let p = save_cursor_command().unwrap().compiled(836, 838).unwrap();
    let mut d = p.initial([]);
    put(&mut d, 838, &[true; 50]);
    let err = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 100_000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
}
