//! Minimal Aeneas borrow/return probes, deliberately NOT a ranked counter.
//!
//! Each case changes one ownership or return-shape dimension. They are
//! negative/positive controls for extraction only. They do not establish the
//! semantics of production code imported by the source-linked harness.
//! Every function is an independent source target in hax.toml.

/// Control: returning a `Result` without mutating a vector.
pub fn p0_result_only(value: u64, refuse: bool) -> Result<u64, u8> {
    if refuse { Err(7) } else { Ok(value) }
}

/// Direct mutable borrow, push, then scalar `Ok` return.
pub fn p1_direct_scalar(events: &mut Vec<u64>, value: u64) -> Result<u64, u8> {
    events.push(value);
    Ok(value)
}

/// Direct mutable borrow, push, then return the earlier `Result`.
pub fn p2_direct_result(events: &mut Vec<u64>, value: u64, refuse: bool) -> Result<u64, u8> {
    let outcome = p0_result_only(value, refuse);
    events.push(value);
    outcome
}

/// Control for optional conditional borrow, with scalar `Ok` return.
pub fn p3_optional_scalar(events: &mut Option<&mut Vec<u64>>, value: u64) -> Result<u64, u8> {
    if let Some(output) = events.as_mut() {
        output.push(value);
    }
    Ok(value)
}

/// Optional mutable borrow, push, then return the earlier `Result`.
pub fn p4_optional_result(
    events: &mut Option<&mut Vec<u64>>,
    value: u64,
    refuse: bool,
) -> Result<u64, u8> {
    let outcome = p0_result_only(value, refuse);
    if let Some(output) = events.as_mut() {
        output.push(value);
    }
    outcome
}

/// Direct borrowed sink plus a checked `i128` transition and owned receipt.
pub fn p5_checked_direct(
    events: &mut Vec<Option<i128>>,
    left: i128,
    right: i128,
) -> Result<i128, u8> {
    let outcome = left.checked_add(right).ok_or(9u8);
    events.push(outcome.as_ref().ok().copied());
    outcome
}

/// Same transition and record, with an optional borrowed sink.
pub fn p6_checked_optional(
    events: &mut Option<&mut Vec<Option<i128>>>,
    left: i128,
    right: i128,
) -> Result<i128, u8> {
    let outcome = left.checked_add(right).ok_or(9u8);
    if let Some(output) = events.as_mut() {
        output.push(outcome.as_ref().ok().copied());
    }
    outcome
}

/// Ownership control: no mutable reference crosses the vector append/return.
pub fn p7_checked_owned(
    mut events: Vec<Option<i128>>,
    left: i128,
    right: i128,
) -> (Result<i128, u8>, Vec<Option<i128>>) {
    let outcome = left.checked_add(right).ok_or(9u8);
    events.push(outcome.as_ref().ok().copied());
    (outcome, events)
}

/// Arithmetic control: checked i128 result without vector effects.
pub fn p8_checked_only(left: i128, right: i128) -> Result<i128, u8> {
    left.checked_add(right).ok_or(9u8)
}

/// Container control: option-valued vector payload without arithmetic.
pub fn p9_option_payload(events: &mut Vec<Option<i128>>, value: i128) -> Result<i128, u8> {
    events.push(Some(value));
    Ok(value)
}

/// Direct scalar vector mutation, with a checked result returned afterward.
pub fn p10_checked_scalar_sink(
    events: &mut Vec<i128>,
    left: i128,
    right: i128,
) -> Result<i128, u8> {
    let outcome = left.checked_add(right).ok_or(9u8);
    events.push(left);
    outcome
}

/// Record the checked Option into the vector, but return a fresh Ok.
pub fn p11_checked_option_sink(
    events: &mut Vec<Option<i128>>,
    left: i128,
    right: i128,
) -> Result<i128, u8> {
    let observed = left.checked_add(right);
    events.push(observed);
    Ok(left)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn return_shapes_and_first_refusal_are_preserved() {
        assert_eq!(p0_result_only(11, false), Ok(11));
        assert_eq!(p0_result_only(11, true), Err(7));

        let mut direct = vec![5];
        assert_eq!(p1_direct_scalar(&mut direct, 11), Ok(11));
        assert_eq!(p2_direct_result(&mut direct, 13, true), Err(7));
        assert_eq!(direct, vec![5, 11, 13]);

        let mut optional = vec![5];
        assert_eq!(p3_optional_scalar(&mut Some(&mut optional), 11), Ok(11));
        assert_eq!(
            p4_optional_result(&mut Some(&mut optional), 13, true),
            Err(7)
        );
        assert_eq!(optional, vec![5, 11, 13]);

        let mut absent = None;
        assert_eq!(p3_optional_scalar(&mut absent, 11), Ok(11));
        assert_eq!(p4_optional_result(&mut absent, 13, true), Err(7));
        assert!(absent.is_none());
    }

    #[test]
    fn arithmetic_option_payload_and_result_controls_are_distinct() {
        assert_eq!(p8_checked_only(2, 3), Ok(5));
        assert_eq!(p8_checked_only(i128::MAX, 1), Err(9));

        let mut option_payload = Vec::new();
        assert_eq!(p9_option_payload(&mut option_payload, 7), Ok(7));
        assert_eq!(option_payload, vec![Some(7)]);

        let mut scalar_events = Vec::new();
        assert_eq!(p10_checked_scalar_sink(&mut scalar_events, 2, 3), Ok(5));
        assert_eq!(
            p10_checked_scalar_sink(&mut scalar_events, i128::MAX, 1),
            Err(9)
        );
        assert_eq!(scalar_events, vec![2, i128::MAX]);

        let mut option_events = Vec::new();
        assert_eq!(p11_checked_option_sink(&mut option_events, 2, 3), Ok(2));
        assert_eq!(
            p11_checked_option_sink(&mut option_events, i128::MAX, 1),
            Ok(i128::MAX)
        );
        assert_eq!(option_events, vec![Some(5), None]);
    }

    #[test]
    fn checked_addition_records_success_and_failure_before_return() {
        let mut direct = Vec::new();
        assert_eq!(p5_checked_direct(&mut direct, 2, 3), Ok(5));
        assert_eq!(p5_checked_direct(&mut direct, i128::MAX, 1), Err(9));
        assert_eq!(direct, vec![Some(5), None]);

        let mut optional = Vec::new();
        assert_eq!(p6_checked_optional(&mut Some(&mut optional), 2, 3), Ok(5));
        assert_eq!(
            p6_checked_optional(&mut Some(&mut optional), i128::MAX, 1),
            Err(9)
        );
        assert_eq!(optional, direct);

        let mut absent = None;
        assert_eq!(p6_checked_optional(&mut absent, i128::MAX, 1), Err(9));
        assert!(absent.is_none());

        let (result, owned) = p7_checked_owned(vec![Some(2)], i128::MAX, 1);
        assert_eq!(result, Err(9));
        assert_eq!(owned, vec![Some(2), None]);
    }
}
