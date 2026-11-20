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

/// Verify source-bound local guards in O(n+e) word operations and O(1)
/// auxiliary storage (outside the input/certificate and diagnostic error).
///
/// This function does not construct connected components or trust DSU roots.
/// An accepted certificate supplies paths from every vertex to a real root
/// using strictly decreasing ranks and actual source edges.
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
    for &(a, b) in source_edges {
        if a >= n || b >= n {
            return Err(Error::Invalid("source edge outside declared region".into()));
        }
    }
    for &label in &certificate.labels {
        if label >= c {
            return Err(Error::Invalid(
                "ranked certificate label outside range".into(),
            ));
        }
    }
    for (class, &root) in certificate.roots.iter().enumerate() {
        if root >= n
            || certificate.labels[root] != class
            || certificate.parent_edge_indices[root].is_some()
            || certificate.rank[root] != 0
        {
            return Err(Error::Invalid("invalid ranked component root".into()));
        }
    }
    for &(a, b) in source_edges {
        if certificate.labels[a] != certificate.labels[b] {
            return Err(Error::Invalid("source edge crosses claimed classes".into()));
        }
    }

    let mut parent_links = 0usize;
    for (vertex, parent_index) in certificate.parent_edge_indices.iter().enumerate() {
        let class = certificate.labels[vertex];
        match parent_index {
            None => {
                if vertex != certificate.roots[class] || certificate.rank[vertex] != 0 {
                    return Err(Error::Invalid("unjustified ranked component root".into()));
                }
            }
            Some(index) => {
                let &(a, b) = source_edges.get(*index).ok_or_else(|| {
                    Error::Invalid("ranked parent edge absent from source".into())
                })?;
                let parent = if a == vertex {
                    b
                } else if b == vertex {
                    a
                } else {
                    return Err(Error::Invalid("ranked parent edge misses vertex".into()));
                };
                if certificate.labels[parent] != class
                    || certificate.rank[parent] >= certificate.rank[vertex]
                {
                    return Err(Error::Invalid(
                        "ranked parent does not preserve label and decrease rank".into(),
                    ));
                }
                parent_links += 1;
            }
        }
    }
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

fn checked_component_product_step_with<F>(
    products: &mut [[i128; 2]],
    class: usize,
    weights: [i128; 2],
    arithmetic: &mut F,
) -> Result<(), Error>
where
    F: FnMut(ArithmeticKind, i128, i128) -> Result<i128, Error>,
{
    let slot = products
        .get_mut(class)
        .ok_or_else(|| Error::Invalid("component product index outside range".into()))?;
    let zero = arithmetic(ArithmeticKind::Mul, slot[0], weights[0])?;
    let one = arithmetic(ArithmeticKind::Mul, slot[1], weights[1])?;
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
    checked_component_product_step_with(products, class, weights, &mut checked_arithmetic)
}

fn checked_component_product_scan_with<F>(
    products: &mut [[i128; 2]],
    labels: &[usize],
    weights: &[[i128; 2]],
    arithmetic: &mut F,
) -> Result<(), Error>
where
    F: FnMut(ArithmeticKind, i128, i128) -> Result<i128, Error>,
{
    if labels.len() != weights.len() {
        return Err(Error::Invalid(
            "component scan label and weight widths disagree".into(),
        ));
    }
    for (&class, &weight) in labels.iter().zip(weights.iter()) {
        checked_component_product_step_with(products, class, weight, arithmetic)?;
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
    checked_component_product_scan_with(products, labels, weights, &mut checked_arithmetic)
}

fn checked_component_product_finish_with<F>(
    products: &[[i128; 2]],
    arithmetic: &mut F,
) -> Result<i128, Error>
where
    F: FnMut(ArithmeticKind, i128, i128) -> Result<i128, Error>,
{
    let mut value = 1i128;
    for &[zero, one] in products {
        let local = arithmetic(ArithmeticKind::Add, zero, one)?;
        value = arithmetic(ArithmeticKind::Mul, value, local)?;
    }
    Ok(value)
}

/// Finish the component array in class order without modifying the source.
/// Refuse overflow immediately, even when a later class contains zero.
pub fn checked_component_product_finish(products: &[[i128; 2]]) -> Result<i128, Error> {
    checked_component_product_finish_with(products, &mut checked_arithmetic)
}

fn contract_checked_ranked_weights_with<F>(
    weights: &[[i128; 2]],
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
    arithmetic: &mut F,
) -> Result<RankedCountReceipt, Error>
where
    F: FnMut(ArithmeticKind, i128, i128) -> Result<i128, Error>,
{
    // This rechecks the *supplied* graph and certificate on every execution.
    let verified = verify_ranked_component_certificate(weights.len(), source_edges, certificate)?;
    let mut products = vec![[1i128, 1i128]; verified.components];
    checked_component_product_scan_with(
        &mut products,
        &certificate.labels,
        weights,
        arithmetic,
    )?;
    let value = checked_component_product_finish_with(&products, arithmetic)?;
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
    contract_checked_ranked_weights_with(
        weights,
        source_edges,
        certificate,
        &mut checked_arithmetic,
    )
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
    let result = contract_checked_ranked_weights_with(
        weights,
        source_edges,
        certificate,
        &mut |kind, left, right| {
            let outcome = checked_arithmetic(kind, left, right);
            operations.push(ArithmeticReceipt {
                kind,
                left,
                right,
                observed: outcome.as_ref().ok().copied(),
            });
            outcome
        },
    );
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
