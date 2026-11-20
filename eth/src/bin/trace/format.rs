//! Wire-format helpers shared by source-comparison trace binaries.
//! These render bits in physical stack order; they do not normalize or reverse them.

use lean_eth_reference::bit_program::Config;

/// A source-machine Boolean bit in the text trace protocol.
pub(crate) fn bit_char(bit: bool) -> char {
    if bit { '1' } else { '0' }
}

/// Encode bits without changing their source order.
pub(crate) fn bits(values: impl IntoIterator<Item = bool>) -> String {
    values.into_iter().map(bit_char).collect()
}

/// Read a physical stack as a wire-format bit string.
pub(crate) fn stack_bits<const R: usize, const S: usize>(
    state: &Config<R, S>,
    port: usize,
) -> String {
    bits(state.stacks[port].iter().copied())
}

#[cfg(test)]
mod tests {
    use super::{bit_char, bits};

    #[test]
    fn bit_trace_preserves_order_and_empty_words() {
        assert_eq!(bit_char(false), '0');
        assert_eq!(bit_char(true), '1');
        assert_eq!(bits([]), "");
        assert_eq!(bits([false, true, true, false]), "0110");
    }
}
