//! Full source normalizer through the actual Native 80x1220 register/stack map.
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_outer_normalization;
use std::collections::VecDeque;
fn unary(n: usize) -> Vec<bool> {
    let mut a = vec![true; n];
    a.push(false);
    a
}
fn frame(xs: &[bool]) -> Vec<bool> {
    let mut a = Vec::new();
    for x in xs {
        a.extend([true, *x]);
    }
    a.push(false);
    a
}
fn list<T>(rows: &[T], to_bits: impl Fn(&T) -> Vec<bool>) -> Vec<bool> {
    let mut a = Vec::new();
    for row in rows {
        a.push(true);
        a.extend(frame(&to_bits(row)));
    }
    a.push(false);
    a
}
fn formula(rows: &[Vec<usize>]) -> Vec<bool> {
    list(rows, |row| list(row, |v| unary(*v)))
}
#[test]
fn native_normalization_lift_preserves_protected_ambient_frame() {
    let p = native_outer_normalization::program().unwrap();
    for rows in [
        vec![],
        vec![vec![]],
        vec![vec![0]],
        vec![vec![0, 1], vec![2, 2], vec![0, 2], vec![0], vec![0, 2, 4]],
    ] {
        let mut c = p.initial(Vec::new());
        c.stacks[1218] = VecDeque::from(formula(&rows));
        c.stacks[256] = VecDeque::from(unary(8));
        c.stacks[267] = VecDeque::from(vec![false, false, false, true]);
        c.stacks[1216] = VecDeque::from(vec![true, false, true]);
        c.regs[43] = true;
        c.regs[79] = true;
        p.run(&mut c, RunLimits::default()).unwrap();
        assert_eq!(c.stacks[256].iter().copied().collect::<Vec<_>>(), unary(8));
        assert_eq!(
            c.stacks[267].iter().copied().collect::<Vec<_>>(),
            vec![false, false, false, true]
        );
        assert_eq!(
            c.stacks[1216].iter().copied().collect::<Vec<_>>(),
            vec![true, false, true]
        );
        assert!(c.regs[43] && c.regs[79]);
        assert!(c.stacks[1218].iter().any(|b| !*b));
        for i in 0..16 {
            if i != 13 {
                assert!(c.stacks[i].is_empty());
            }
        }
        assert_eq!(c.pc, None);
    }
}
