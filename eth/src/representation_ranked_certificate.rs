//! Source-edge-bound component certificates with locally checked parent ranks.
//!
//! This checker is independent of the producing union-find and of its
//! forest traversal. It reads only labels, roots, parent source-edge indices,
//! ranks, and the original edge list. Every parent step decreases rank,
//! which makes global path search unnecessary.
//!
//! Lean's ACC.RankedComponentCertificate proves these *mathematical local
//! conditions* imply the exact graph quotient and contraction. Formal
//! correspondence of these Rust loops to that Lean checker is still open.

use crate::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RankedComponentCertificate {
    /// Dense class identifiers in 0..roots.len(), one per vertex.
    pub labels: Vec<usize>,
    /// One vertex representative per class.
    pub roots: Vec<usize>,
    /// None exactly for roots; otherwise an original source-edge index.
    pub parent_edge_indices: Vec<Option<usize>>,
    /// Nonnegative descending rank. Roots have rank zero.
    pub rank: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedRankedCertificate {
    pub variables: usize,
    pub source_edges: usize,
    pub components: usize,
    pub parent_links: usize,
}

// Each helper examines the original source collection in order. Error
// decisions are recorded and returned only *after* the scan exits: this
// preserves first-refusal behavior while avoiding Aeneas-unsupported early
// function returns from a loop. No suffix is visited after the first failure.
fn check_edge_bounds(n: usize, source_edges: &[(usize, usize)]) -> Result<(), Error> {
    let mut invalid = false;
    let mut index = 0;
    while index < source_edges.len() && !invalid {
        let (a, b) = source_edges[index];
        // Keep the Bool state explicit for source-to-Lean extraction. The
        // checks are pure and read both already-loaded endpoint values.
        // This is equivalent to a >= n || b >= n on all valid usize inputs.
        if a >= n {
            invalid = true;
        }
        if b >= n {
            invalid = true;
        }
        index += 1;
    }
    if invalid {
        Err(Error::Invalid("source edge outside declared region".into()))
    } else {
        Ok(())
    }
}

fn check_label_bounds(classes: usize, labels: &[usize]) -> Result<(), Error> {
    let mut invalid = false;
    let mut index = 0;
    while index < labels.len() && !invalid {
        invalid = labels[index] >= classes;
        index += 1;
    }
    if invalid {
        Err(Error::Invalid(
            "ranked certificate label outside range".into(),
        ))
    } else {
        Ok(())
    }
}

fn check_declared_roots(n: usize, certificate: &RankedComponentCertificate) -> Result<(), Error> {
    let mut invalid = false;
    let mut class = 0;
    while class < certificate.roots.len() && !invalid {
        let root = certificate.roots[class];
        invalid = root >= n
            || certificate.labels[root] != class
            || certificate.parent_edge_indices[root].is_some()
            || certificate.rank[root] != 0;
        class += 1;
    }
    if invalid {
        Err(Error::Invalid("invalid ranked component root".into()))
    } else {
        Ok(())
    }
}

fn check_edge_class_closure(
    source_edges: &[(usize, usize)],
    labels: &[usize],
) -> Result<(), Error> {
    let mut invalid = false;
    let mut index = 0;
    while index < source_edges.len() && !invalid {
        let (a, b) = source_edges[index];
        invalid = labels[a] != labels[b];
        index += 1;
    }
    if invalid {
        Err(Error::Invalid("source edge crosses claimed classes".into()))
    } else {
        Ok(())
    }
}

// Validation of one parent witness is pure and returns a scalar refusal
// code. It is deliberately outside the indexed scan, so the scan does not
// have to join nested Rust borrow contexts or allocate error strings.
// Refusal codes are converted to the original diagnostic at the end.
fn parent_refusal_code(
    vertex: usize,
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
) -> u8 {
    let class = certificate.labels[vertex];
    match certificate.parent_edge_indices[vertex] {
        None => {
            if vertex != certificate.roots[class] || certificate.rank[vertex] != 0 {
                1
            } else {
                0
            }
        }
        Some(index) => {
            if index >= source_edges.len() {
                return 2;
            }
            let (a, b) = source_edges[index];
            if a != vertex && b != vertex {
                return 3;
            }
            let parent = if a == vertex { b } else { a };
            if certificate.labels[parent] != class
                || certificate.rank[parent] >= certificate.rank[vertex]
            {
                4
            } else {
                0
            }
        }
    }
}

fn check_ranked_parents(
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
) -> Result<usize, Error> {
    let mut parent_links = 0usize;
    let mut refusal = 0u8;
    let mut vertex = 0usize;
    while vertex < certificate.parent_edge_indices.len() && refusal == 0 {
        refusal = parent_refusal_code(vertex, source_edges, certificate);
        if refusal == 0 && certificate.parent_edge_indices[vertex].is_some() {
            parent_links += 1;
        }
        vertex += 1;
    }
    match refusal {
        0 => Ok(parent_links),
        1 => Err(Error::Invalid("unjustified ranked component root".into())),
        2 => Err(Error::Invalid(
            "ranked parent edge absent from source".into(),
        )),
        3 => Err(Error::Invalid("ranked parent edge misses vertex".into())),
        4 => Err(Error::Invalid(
            "ranked parent does not preserve label and decrease rank".into(),
        )),
        _ => Err(Error::Invalid("unknown ranked parent refusal".into())),
    }
}

/// Verify source-bound local guards in O(n+e) word operations and O(1)
/// auxiliary storage (outside the input/certificate and diagnostic error).
///
/// All five guards retain the original order and immediate refusal behavior,
/// but their separately named loops also form smaller extraction and proof
/// obligations. A valid certificate supplies a strictly decreasing original
/// source-edge parent path to a root for every vertex.
pub fn verify_ranked_component_certificate(
    variable_count: usize,
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
) -> Result<VerifiedRankedCertificate, Error> {
    let n = variable_count;
    let c = certificate.roots.len();
    if certificate.labels.len() != n
        || certificate.parent_edge_indices.len() != n
        || certificate.rank.len() != n
        || c > n
    {
        return Err(Error::Invalid("ranked certificate widths disagree".into()));
    }
    check_edge_bounds(n, source_edges)?;
    check_label_bounds(c, &certificate.labels)?;
    check_declared_roots(n, certificate)?;
    check_edge_class_closure(source_edges, &certificate.labels)?;
    let parent_links = check_ranked_parents(source_edges, certificate)?;
    Ok(VerifiedRankedCertificate {
        variables: n,
        source_edges: source_edges.len(),
        components: c,
        parent_links,
    })
}

/// Central signed 128-bit arithmetic boundary used by the certified
/// component-counter helpers. Refusal is explicit; overflow never wraps.
pub fn checked_i128_add(a: i128, b: i128) -> Result<i128, Error> {
    a.checked_add(b).ok_or(Error::Overflow)
}

/// See `checked_i128_add`. The mathematical model is the signed
/// two's-complement BitVec 128 signed-overflow gate, not modular arithmetic.
pub fn checked_i128_mul(a: i128, b: i128) -> Result<i128, Error> {
    a.checked_mul(b).ok_or(Error::Overflow)
}

/// Which *actual* checked arithmetic helper an untrusted receipt sampled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithmeticKind {
    Add,
    Mul,
}

/// A single recorded invocation of the production checked-i128 helper.
/// The observed result is untrusted until checked independently.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArithmeticReceipt {
    pub kind: ArithmeticKind,
    pub left: i128,
    pub right: i128,
    pub observed: Option<i128>,
}

/// Execute the same arithmetic helper used in the production contraction
/// and record its concrete outcome for independent translation validation.
/// This function deliberately does not claim to instrument every operation
/// of a larger counting run.
pub fn observe_checked_arithmetic(
    kind: ArithmeticKind,
    left: i128,
    right: i128,
) -> ArithmeticReceipt {
    let observed = match kind {
        ArithmeticKind::Add => checked_i128_add(left, right).ok(),
        ArithmeticKind::Mul => checked_i128_mul(left, right).ok(),
    };
    ArithmeticReceipt {
        kind,
        left,
        right,
        observed,
    }
}

// All scan, finalization, and contraction paths share the same arithmetic
// transition function. The receipt variant observes this *one* execution
// rather than independently re-evaluating a second implementation.
fn checked_arithmetic(kind: ArithmeticKind, left: i128, right: i128) -> Result<i128, Error> {
    match kind {
        ArithmeticKind::Add => checked_i128_add(left, right),
        ArithmeticKind::Mul => checked_i128_mul(left, right),
    }
}

// Recording is explicit, not a generic FnMut callback. Both ordinary and
// traced paths share this exact arithmetic transition and mutation order.
// None has no allocation and does not change the arithmetic outcome.
// The first refused operation is recorded before its caller stops.
fn checked_arithmetic_and_record(
    kind: ArithmeticKind,
    left: i128,
    right: i128,
    observations: &mut Option<&mut Vec<ArithmeticReceipt>>,
) -> Result<i128, Error> {
    let outcome = checked_arithmetic(kind, left, right);
    if let Some(events) = observations.as_mut() {
        events.push(ArithmeticReceipt {
            kind,
            left,
            right,
            observed: outcome.as_ref().ok().copied(),
        });
    }
    outcome
}

fn checked_component_product_step_with(
    products: &mut [[i128; 2]],
    class: usize,
    weights: [i128; 2],
    observations: &mut Option<&mut Vec<ArithmeticReceipt>>,
) -> Result<(), Error> {
    let slot = products
        .get_mut(class)
        .ok_or_else(|| Error::Invalid("component product index outside range".into()))?;
    let zero =
        checked_arithmetic_and_record(ArithmeticKind::Mul, slot[0], weights[0], observations)?;
    let one =
        checked_arithmetic_and_record(ArithmeticKind::Mul, slot[1], weights[1], observations)?;
    *slot = [zero, one];
    Ok(())
}

/// One source-vertex update to the indexed component-product array.
/// Both checked multiplications complete before the slot is changed.
/// A failed update leaves this slot unchanged.
pub fn checked_component_product_step(
    products: &mut [[i128; 2]],
    class: usize,
    weights: [i128; 2],
) -> Result<(), Error> {
    let mut observations = None;
    checked_component_product_step_with(products, class, weights, &mut observations)
}

fn checked_component_product_scan_with(
    products: &mut [[i128; 2]],
    labels: &[usize],
    weights: &[[i128; 2]],
    observations: &mut Option<&mut Vec<ArithmeticReceipt>>,
) -> Result<(), Error> {
    if labels.len() != weights.len() {
        return Err(Error::Invalid(
            "component scan label and weight widths disagree".into(),
        ));
    }
    for (&class, &weight) in labels.iter().zip(weights.iter()) {
        checked_component_product_step_with(products, class, weight, observations)?;
    }
    Ok(())
}

/// Scan a vertex-major stream. An arithmetic refusal stops immediately;
/// earlier completed vertices are not rolled back. Width errors refuse
/// before any arithmetic is performed.
pub fn checked_component_product_scan(
    products: &mut [[i128; 2]],
    labels: &[usize],
    weights: &[[i128; 2]],
) -> Result<(), Error> {
    let mut observations = None;
    checked_component_product_scan_with(products, labels, weights, &mut observations)
}

fn checked_component_product_finish_with(
    products: &[[i128; 2]],
    observations: &mut Option<&mut Vec<ArithmeticReceipt>>,
) -> Result<i128, Error> {
    let mut value = 1i128;
    for &[zero, one] in products {
        let local = checked_arithmetic_and_record(ArithmeticKind::Add, zero, one, observations)?;
        value = checked_arithmetic_and_record(ArithmeticKind::Mul, value, local, observations)?;
    }
    Ok(value)
}

/// Finish the component array in class order without modifying the source.
/// Refuse overflow immediately, even when a later class contains zero.
pub fn checked_component_product_finish(products: &[[i128; 2]]) -> Result<i128, Error> {
    let mut observations = None;
    checked_component_product_finish_with(products, &mut observations)
}

fn contract_checked_ranked_weights_with(
    weights: &[[i128; 2]],
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
    observations: &mut Option<&mut Vec<ArithmeticReceipt>>,
) -> Result<RankedCountReceipt, Error> {
    // Recheck the supplied graph and certificate before any arithmetic.
    let verified = verify_ranked_component_certificate(weights.len(), source_edges, certificate)?;
    let mut products = vec![[1i128, 1i128]; verified.components];
    checked_component_product_scan_with(&mut products, &certificate.labels, weights, observations)?;
    let value = checked_component_product_finish_with(&products, observations)?;
    let multiplications = weights
        .len()
        .checked_mul(2)
        .and_then(|count| count.checked_add(verified.components))
        .ok_or(Error::Overflow)?;
    Ok(RankedCountReceipt {
        value,
        variable_count: verified.variables,
        component_count: verified.components,
        checked_additions: verified.components,
        checked_multiplications: multiplications,
    })
}

/// Exact contraction from source-bound, locally verified class labels.
pub fn contract_checked_ranked_weights(
    weights: &[[i128; 2]],
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
) -> Result<RankedCountReceipt, Error> {
    contract_checked_ranked_weights_with(weights, source_edges, certificate, &mut None)
}

/// Observe *every checked arithmetic invocation* of this particular Rust
/// source-level contraction run, in order, including the first refusal.
/// The same checked helper and control-flow body serve the ordinary counter.
/// This is executable instrumentation, not a formal Rust/compiler refinement.
///
/// On invalid input or certificate rejection no arithmetic is invoked.
/// The returned error and trace are both untrusted until independently checked.
pub fn contract_checked_ranked_weights_with_trace(
    weights: &[[i128; 2]],
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
) -> (Result<RankedCountReceipt, Error>, Vec<ArithmeticReceipt>) {
    let mut operations = Vec::new();
    let result = {
        let mut observations = Some(&mut operations);
        contract_checked_ranked_weights_with(weights, source_edges, certificate, &mut observations)
    };
    (result, operations)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RankedCountReceipt {
    pub value: i128,
    pub variable_count: usize,
    pub component_count: usize,
    pub checked_additions: usize,
    pub checked_multiplications: usize,
}
