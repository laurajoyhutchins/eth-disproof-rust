//! Execute the literal four-command Native frontend from source CNF encodings.
//! Semantic reference checks appear only in tests and never drive the machine.
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_frontend;
use lean_eth_reference::{Cnf, Error};

fn bits(xs: &str) -> Vec<bool> {
    xs.bytes().map(|c| c == b'1').collect()
}
fn word<const R: usize, const S: usize>(cfg: &Config<R, S>, port: usize) -> Vec<bool> {
    cfg.stacks[port].iter().copied().collect()
}
fn unary(n: usize) -> Vec<bool> {
    let mut xs = vec![true; n];
    xs.push(false);
    xs
}
fn binary(mut n: usize) -> Vec<bool> {
    let mut xs = vec![];
    while n != 0 {
        xs.push(n % 2 == 1);
        n >>= 1;
    }
    xs
}
fn check_frontend(cnf: Cnf) {
    let source = cnf.encode_lean();
    let expected = cnf.normalize().encode_lean();
    let n = cnf.variables();
    let normalized_body = bits(&expected[n + 1..]);
    let physical_input = bits(&source);
    let program = native_frontend::program().unwrap();
    assert_eq!(program.input_stack(), 256);
    assert_eq!(program.output_stack(), 263);
    let mut cfg = program.initial(physical_input.clone());
    let stats = program
        .run(
            &mut cfg,
            RunLimits {
                max_steps: 20_000_000,
                max_stack_bits: 300_000,
            },
        )
        .unwrap();
    assert_eq!(cfg.pc, None, "frontend did not halt");
    assert_eq!(
        word(&cfg, 256),
        physical_input,
        "source encoding was mutated"
    );
    assert_eq!(word(&cfg, 258), unary(n), "ambient unary header");
    assert_eq!(word(&cfg, 267), binary(n), "binary variable count");
    assert_eq!(word(&cfg, 265), normalized_body, "normalized body");
    for i in 0..1220 {
        if ![256, 258, 265, 267].contains(&i) {
            assert!(cfg.stacks[i].is_empty(), "work stack {i} was not cleaned");
        }
    }
    assert!(stats.instructions > 0);
    assert!(stats.peak_stack_bits >= source.len());
}

#[test]
fn exact_source_frontend_empty_formula_and_empty_clause() {
    check_frontend(Cnf::from_signed(0, &[]).unwrap());
    check_frontend(Cnf::from_signed(3, &[]).unwrap());
    check_frontend(Cnf::from_signed(0, &[&[]]).unwrap());
    check_frontend(Cnf::from_signed(4, &[&[]]).unwrap());
}

#[test]
fn exact_source_frontend_normalizes_canonical_cnf_cases() {
    check_frontend(Cnf::from_signed(1, &[&[1]]).unwrap());
    check_frontend(Cnf::from_signed(2, &[&[1], &[-1, 2]]).unwrap());
    check_frontend(Cnf::from_signed(3, &[&[1, -1], &[2], &[2, 3]]).unwrap());
    check_frontend(Cnf::from_signed(4, &[&[1, 2], &[1], &[1, 2, 3], &[-2, 3]]).unwrap());
    check_frontend(Cnf::from_signed(5, &[&[-1, 2], &[2, 3], &[2, 3], &[4, 5]]).unwrap());
}

#[test]
fn source_frontend_random_canonical_inputs_preserve_full_abi() {
    let mut seed = 0xf99fa92de118f925_u64;
    let mut random = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed
    };
    for _ in 0..18 {
        let n = (random() % 4 + 1) as usize;
        let count = (random() % 6) as usize;
        let rows = (0..count)
            .map(|_| {
                let m = (random() % 4) as usize;
                (0..m)
                    .map(|_| {
                        let var = (random() % n as u64 + 1) as i64;
                        if random() & 1 == 0 { -var } else { var }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let clauses = rows.iter().map(Vec::as_slice).collect::<Vec<_>>();
        check_frontend(Cnf::from_signed(n, &clauses).unwrap());
    }
}

#[test]
fn source_frontend_refuses_insufficient_budget_without_fabricating_success() {
    let input = Cnf::from_signed(3, &[&[1, -2], &[3]])
        .unwrap()
        .encode_lean();
    let program = native_frontend::program().unwrap();
    let mut cfg = program.initial(bits(&input));
    let failure = program
        .run(
            &mut cfg,
            RunLimits {
                max_steps: 8,
                max_stack_bits: 4000,
            },
        )
        .unwrap_err();
    assert!(matches!(failure, Error::Capacity(_)));
    assert!(cfg.pc.is_some());
    assert!(cfg.stacks[265].is_empty());
    assert!(cfg.stacks[263].is_empty());
}
