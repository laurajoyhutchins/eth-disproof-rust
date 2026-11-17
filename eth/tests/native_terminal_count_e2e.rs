//! End-to-end physical count tests: these never ask the host SAT oracle
//! to produce a count. All assertions come AFTER the machine halts.
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_terminal_count::{count_terminal, count_word_decimal};
use lean_eth_reference::{Cnf, Error};

fn limits() -> RunLimits {
    RunLimits {
        max_steps: 20_000_000,
        max_stack_bits: 300_000,
    }
}
fn check(cnf: Cnf, expected: &str, positive: bool) {
    let count = count_terminal(&cnf, limits()).expect("complete source-native terminal path");
    assert_eq!(count_word_decimal(&count.count_lsb), expected);
    assert_eq!(count.positive, positive);
    assert!(count.stages.iter().all(|stats| stats.instructions > 0));
    assert_eq!(
        count.total_instructions,
        count.stages.iter().map(|s| s.instructions).sum::<u64>()
    );
    assert!(count.peak_stack_bits >= cnf.encode_lean().len());
}

#[test]
fn source_machine_counts_empty_formula_with_unused_variables() {
    check(Cnf::from_signed(0, &[]).unwrap(), "1", true);
    check(Cnf::from_signed(3, &[]).unwrap(), "8", true);
}
#[test]
fn source_machine_counts_empty_clause_as_zero() {
    check(Cnf::from_signed(0, &[&[]]).unwrap(), "0", false);
    check(Cnf::from_signed(3, &[&[], &[1, 2]]).unwrap(), "0", false);
}
#[test]
fn source_normalization_can_turn_tautology_into_terminal_count() {
    // The frontend, not the host, removes the tautological clause.
    check(Cnf::from_signed(2, &[&[-1, 1]]).unwrap(), "4", true);
}
#[test]
fn nonterminal_formula_is_not_misrepresented_as_a_zero_count() {
    let result = count_terminal(&Cnf::from_signed(2, &[&[1]]).unwrap(), limits());
    assert!(matches!(result, Err(Error::NotImplemented(_))));
}
#[test]
fn resource_caps_refuse_before_any_count_is_accepted() {
    let cnf = Cnf::from_signed(4, &[]).unwrap();
    let result = count_terminal(
        &cnf,
        RunLimits {
            max_steps: 1,
            max_stack_bits: 300_000,
        },
    );
    assert!(matches!(result, Err(Error::Capacity(_))));
    let result = count_terminal(
        &cnf,
        RunLimits {
            max_steps: 20_000_000,
            max_stack_bits: 0,
        },
    );
    assert!(matches!(result, Err(Error::Capacity(_))));
}
#[test]
fn decimal_formatting_keeps_integer_bits_beyond_u128() {
    let mut word = vec![false; 130];
    word.push(true);
    assert_eq!(
        count_word_decimal(&word),
        "1361129467683753853853498429727072845824"
    );
    assert_eq!(count_word_decimal(&[]), "0");
    assert_eq!(count_word_decimal(&[false, false]), "0");
    assert_eq!(count_word_decimal(&[true, false, true]), "5");
}
