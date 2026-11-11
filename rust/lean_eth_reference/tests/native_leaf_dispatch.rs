//! The callback is a physical test marker, NOT a semantic or executable leaf.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd, Config, RunLimits};
use lean_eth_reference::native_leaf_dispatch;
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, p: usize, xs: &[bool]) {
    c.stacks[p] = VecDeque::from(xs.to_vec());
}
fn take<const R: usize, const S: usize>(c: &Config<R, S>, p: usize) -> Vec<bool> {
    c.stacks[p].iter().copied().collect()
}
fn frame(xs: &[bool]) -> Vec<bool> {
    let mut a = Vec::new();
    for x in xs {
        a.push(true);
        a.push(*x);
    }
    a.push(false);
    a
}
fn encoding(rows: &[Vec<bool>]) -> Vec<bool> {
    let mut a = Vec::new();
    for x in rows {
        a.push(true);
        a.extend(frame(x));
    }
    a.push(false);
    a
}
fn unary(n: usize) -> Vec<bool> {
    let mut a = vec![true; n];
    a.push(false);
    a
}
fn power(n: usize) -> Vec<bool> {
    let mut a = vec![false; n];
    a.push(true);
    a
}

fn marker() -> Cmd<80, 1220> {
    // This writes only a sentinel register and stack, NEVER the count stack.
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 79,
            value: true,
        }),
        Cmd::Atom(Atom::Push {
            stack: 1200,
            src: 79,
        }),
    )
}

#[test]
fn source_dispatch_executes_only_real_nonterminal_branch() {
    let p = native_leaf_dispatch::program(marker()).unwrap();
    for n in 0..=6 {
        for (rows, terminal) in [
            (vec![], 0usize),
            (vec![vec![]], 2usize),
            (vec![vec![false]], 1usize),
            (vec![vec![false], vec![]], 1usize),
            (vec![vec![true], vec![false, true]], 2usize),
        ] {
            let body = encoding(&rows);
            let mut c = p.initial(body.clone());
            put(&mut c, 258, &unary(n));
            put(&mut c, 263, &[true, false, true]);
            put(&mut c, 268, &[true]);
            put(&mut c, 269, &[true, false]);
            put(&mut c, 256, &[false, true]);
            put(&mut c, 1216, &[true, false]);
            p.run(&mut c, RunLimits::default()).unwrap();
            let expected = match terminal {
                0 => power(n),
                1 => vec![false],
                _ => vec![],
            };
            assert_eq!(take(&c, 263), expected);
            assert_eq!(c.regs[79], terminal == 2, "rows={rows:?}");
            assert_eq!(
                take(&c, 1200),
                if terminal == 2 { vec![true] } else { vec![] }
            );
            assert_eq!(take(&c, 265), body);
            assert_eq!(take(&c, 258), unary(n));
            assert_eq!(take(&c, 256), vec![false, true]);
            assert_eq!(take(&c, 1216), vec![true, false]);
            assert!(c.stacks[268].is_empty() && c.stacks[269].is_empty());
            assert_eq!(c.pc, None);
        }
    }
}

#[test]
fn generic_dispatch_must_run_a_supplied_command_not_an_oracle() {
    let callback = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 78,
            value: true,
        }),
        Cmd::Atom(Atom::Push {
            stack: 1199,
            src: 78,
        }),
    );
    let p = native_leaf_dispatch::program(callback).unwrap();
    let mut c = p.initial(encoding(&[vec![true]]));
    put(&mut c, 258, &unary(2));
    p.run(&mut c, RunLimits::default()).unwrap();
    assert_eq!(take(&c, 1199), vec![true]);
    assert!(c.regs[78]);
    assert!(c.stacks[263].is_empty());
}

#[test]
fn guard_disallows_reporting_partial_execution_as_success() {
    let p = native_leaf_dispatch::program(marker()).unwrap();
    let mut c = p.initial(encoding(&[vec![false], vec![true]]));
    put(&mut c, 258, &unary(1));
    let err = p
        .run(
            &mut c,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 10000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(c.pc.is_some());
    assert!(c.stacks[1200].is_empty());
}
