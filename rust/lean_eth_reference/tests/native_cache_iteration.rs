use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_cache_iteration::{
    cache_iteration_program, cache_parse_command, cache_pass_command, cache_pass_program,
    cache_row_command, cache_row_program, emit_record_program, h_build_program,
    scalar_emit_pair_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, i: usize, bits: &[bool]) {
    c.stacks[i] = VecDeque::from(bits.to_vec());
}
fn get<const R: usize, const S: usize>(c: &Config<R, S>, i: usize) -> Vec<bool> {
    c.stacks[i].iter().copied().collect()
}
fn bits(n: u128) -> Vec<bool> {
    if n == 0 {
        return vec![];
    }
    (0..128 - n.leading_zeros())
        .map(|i| (n >> i) & 1 != 0)
        .collect()
}
fn value(w: &[bool]) -> u128 {
    w.iter()
        .enumerate()
        .fold(0, |n, (i, b)| n + if *b { 1u128 << i } else { 0 })
}
fn frame_rev(w: &[bool]) -> Vec<bool> {
    let mut out = Vec::new();
    for &b in w.iter().rev() {
        out.push(true);
        out.push(b);
    }
    out.push(false);
    out
}
fn encode(row: &[Vec<bool>]) -> Vec<bool> {
    let mut out = Vec::new();
    for w in row {
        out.push(true);
        out.extend(frame_rev(w));
        out.push(false);
    }
    out.push(false);
    out
}
fn decode(stream: &[bool]) -> Vec<Vec<bool>> {
    let mut at = 0;
    let mut out = Vec::new();
    loop {
        assert!(at < stream.len(), "missing pair tag");
        let tag = stream[at];
        at += 1;
        if !tag {
            assert_eq!(at, stream.len(), "unconsumed trailing bits");
            return out;
        }
        let mut words = [Vec::new(), Vec::new()];
        for word in &mut words {
            loop {
                assert!(at < stream.len(), "missing frame end");
                let entry = stream[at];
                at += 1;
                if !entry {
                    break;
                }
                assert!(at < stream.len(), "missing frame bit");
                word.push(stream[at]);
                at += 1;
            }
        }
        assert!(words[1].is_empty(), "negative H component must be zero");
        words[0].reverse();
        out.push(words[0].clone());
    }
}
fn scan(row: &[u128]) -> Vec<u128> {
    let mut carry = 0;
    row.iter()
        .map(|&old| {
            carry = 2 * carry + old;
            carry
        })
        .collect()
}
fn expected(a: usize, r: usize) -> Vec<u128> {
    let mut x = vec![1u128; r];
    for _ in 0..a {
        x = scan(&x);
    }
    x
}

#[test]
fn exact_literal_writer_is_fixed_17_label_table_with_source_entry() {
    let p = emit_record_program().unwrap();
    assert_eq!(p.code().len(), 17);
    assert_eq!(p.entry(), 7);
    assert_eq!(p.input_stack(), 3);
    assert_eq!(p.output_stack(), 2);
    assert_eq!(
        scalar_emit_pair_program().unwrap().code().len(),
        lean_eth_reference::native_cache_iteration::scalar_emit_pair_command()
            .unwrap()
            .size()
            .unwrap()
            + 1
    );
}
#[test]
fn the_real_parser_consumes_both_framed_components_without_reordering() {
    let p = cache_parse_command().unwrap().compiled(15, 2).unwrap();
    for row in [vec![], vec![vec![]], vec![bits(13)], vec![bits(3), bits(7)]] {
        let mut d = p.initial(encode(&row));
        put(&mut d, 16, &[true, false, true]);
        p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(d.regs[7], !row.is_empty());
        if let Some(first) = row.first() {
            assert_eq!(get(&d, 2), *first);
        }
        assert_eq!(get(&d, 16), vec![true, false, true]);
        if row.is_empty() {
            assert!(get(&d, 15).is_empty());
        } else {
            assert_eq!(decode(&get(&d, 15)).len(), row.len() - 1);
        }
    }
}
#[test]
fn cache_row_uses_real_adder_and_preserving_serializer() {
    let p = cache_row_program().unwrap();
    for n in 0..=7 {
        let row: Vec<Vec<bool>> = (0..n).map(|i| bits((i * i + 3 * i + 1) as u128)).collect();
        let mut d = p.initial(encode(&row));
        put(&mut d, 17, &[true, true]);
        let before17 = get(&d, 17);
        p.run(&mut d, RunLimits::default()).unwrap();
        let expected = scan(&row.iter().map(|v| value(v)).collect::<Vec<_>>());
        let out = get(&d, 16);
        let mut parsed =
            decode(&[out.iter().rev().copied().collect::<Vec<_>>(), vec![false]].concat());
        assert_eq!(parsed.len(), n);
        for (i, w) in parsed.drain(..).enumerate() {
            assert_eq!(value(&w), expected[i]);
        }
        assert_eq!(get(&d, 17), before17);
        assert!(get(&d, 2).is_empty() && get(&d, 3).is_empty());
        assert!(get(&d, 15).is_empty());
    }
}
#[test]
fn cache_pass_preserves_row_count_and_writes_valid_encoded_stream() {
    let p = cache_pass_program().unwrap();
    assert_eq!(
        p.code().len(),
        cache_pass_command().unwrap().size().unwrap() + 1
    );
    for n in 0..=7 {
        let row: Vec<Vec<bool>> = (0..n).map(|i| bits((i * 17 + 3) as u128)).collect();
        let mut d = p.initial(encode(&row));
        put(&mut d, 17, &[false, true, false]);
        let before = get(&d, 17);
        p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(get(&d, 17), before);
        assert_eq!(
            decode(&get(&d, 15))
                .iter()
                .map(|w| value(w))
                .collect::<Vec<_>>(),
            scan(&row.iter().map(|v| value(v)).collect::<Vec<_>>())
        );
        assert!(get(&d, 0).is_empty() && get(&d, 16).is_empty());
    }
}
#[test]
fn iteration_executes_unary_height_over_physical_row_stream() {
    let p = cache_iteration_program().unwrap();
    for a in 0..=4 {
        for r in 0..=6 {
            let mut d = p.initial(vec![true; a]);
            put(&mut d, 15, &encode(&vec![vec![true]; r]));
            put(&mut d, 12, &[true, false, true]);
            p.run(
                &mut d,
                RunLimits {
                    max_steps: 2_000_000,
                    max_stack_bits: 1_000_000,
                },
            )
            .unwrap();
            assert_eq!(
                decode(&get(&d, 15))
                    .iter()
                    .map(|w| value(w))
                    .collect::<Vec<_>>(),
                expected(a, r),
                "a={a} r={r}"
            );
            assert!(get(&d, 17).is_empty());
            assert_eq!(get(&d, 12), vec![true, false, true]);
        }
    }
}
#[test]
fn full_h_builder_initializes_and_iterates_from_unary_a_and_r() {
    let p = h_build_program().unwrap();
    for a in 0..=4 {
        for r in 0..=6 {
            let mut d = p.initial(vec![true; a]);
            put(&mut d, 18, &vec![false; r]);
            put(&mut d, 12, &[false, true, true]);
            p.run(
                &mut d,
                RunLimits {
                    max_steps: 2_000_000,
                    max_stack_bits: 1_000_000,
                },
            )
            .unwrap();
            let got = decode(&get(&d, 15));
            assert_eq!(got.len(), r);
            assert_eq!(
                got.iter().map(|w| value(w)).collect::<Vec<_>>(),
                expected(a, r),
                "a={a} r={r}"
            );
            assert!(get(&d, 17).is_empty() && get(&d, 18).is_empty());
            assert_eq!(get(&d, 12), vec![false, true, true]);
        }
    }
}
#[test]
fn compound_program_sizes_are_static_and_do_not_depend_on_runtime_inputs() {
    let p = cache_row_program().unwrap();
    assert_eq!(
        p.code().len(),
        cache_row_command().unwrap().size().unwrap() + 1
    );
    let q = h_build_program().unwrap();
    assert_eq!(
        q.code().len(),
        lean_eth_reference::native_cache_iteration::h_build_command()
            .unwrap()
            .size()
            .unwrap()
            + 1
    );
    assert_ne!(p.code().len(), q.code().len());
}

#[test]
fn scalar_emitter_preserves_both_signed_words_and_exact_source_step_cost() {
    let p = scalar_emit_pair_program().unwrap();
    for left in [
        vec![],
        vec![false],
        vec![true, false, true],
        vec![false, false, false, true],
    ] {
        for right in [
            vec![],
            vec![true],
            vec![false, false],
            vec![true, true, false],
        ] {
            let buffer = vec![true, false, true];
            let mut d = p.initial(left.clone());
            put(&mut d, 1, &right);
            put(&mut d, 2, &buffer);
            let stats = p.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(
                stats.instructions,
                (18 * (left.len() + right.len()) + 39) as u64
            );
            let expected_prefix = [vec![true], frame_rev(&left), frame_rev(&right)].concat();
            assert_eq!(
                get(&d, 2),
                [
                    expected_prefix.into_iter().rev().collect::<Vec<_>>(),
                    buffer
                ]
                .concat()
            );
            assert_eq!(get(&d, 0), left);
            assert_eq!(get(&d, 1), right);
            for i in 3..=6 {
                assert!(get(&d, i).is_empty(), "scratch stack {i}");
            }
        }
    }
}

#[test]
fn iterator_fails_closed_at_instruction_limit_without_claiming_an_answer() {
    let p = cache_iteration_program().unwrap();
    let mut d = p.initial(vec![true; 4]);
    put(&mut d, 15, &encode(&vec![vec![true]; 4]));
    let e = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 12,
                max_stack_bits: 1_000_000,
            },
        )
        .unwrap_err();
    assert!(matches!(e, lean_eth_reference::Error::Capacity(_)));
    assert!(d.pc.is_some());
}
