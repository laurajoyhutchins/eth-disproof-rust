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

/// One source-vertex update to the indexed component-product array.
/// Both checked multiplications complete before the slot is changed.
/// Failed operations (including invalid class indices) leave every slot
/// unmodified, making the successful step a simple atomic refinement target.
pub fn checked_component_product_step(
    products: &mut [[i128; 2]],
    class: usize,
    weights: [i128; 2],
) -> Result<(), Error> {
    let slot = products
        .get_mut(class)
        .ok_or_else(|| Error::Invalid("component product index outside range".into()))?;
    let zero = checked_i128_mul(slot[0], weights[0])?;
    let one = checked_i128_mul(slot[1], weights[1])?;
    *slot = [zero, one];
    Ok(())
}

/// Scan a vertex-major stream, updating the class product table in place.
/// Each individual update is atomic on refusal; earlier completed updates
/// remain visible after a later failure. This is intentionally *not* a
/// transactional whole-scan rollback. Width mismatches refuse before writes.
pub fn checked_component_product_scan(
    products: &mut [[i128; 2]],
    labels: &[usize],
    weights: &[[i128; 2]],
) -> Result<(), Error> {
    if labels.len() != weights.len() {
        return Err(Error::Invalid(
            "component scan label and weight widths disagree".into(),
        ));
    }
    for (&class, &weight) in labels.iter().zip(weights.iter()) {
        checked_component_product_step(products, class, weight)?;
    }
    Ok(())
}

/// Finish a component-product array in dense class order. Each class's two
/// signed products are checked-added before multiplication into the running
/// count. Refusal is immediate, even if later classes could multiply by zero.
/// This immutable pass never alters the component-product array.
pub fn checked_component_product_finish(products: &[[i128; 2]]) -> Result<i128, Error> {
    let mut value = 1i128;
    for &[zero, one] in products {
        let local = checked_i128_add(zero, one)?;
        value = checked_i128_mul(value, local)?;
    }
    Ok(value)
}

/// Exact checked contraction from *verified labels*, not from DSU parents.
/// Overflows refuse instead of silently truncating a signed integer count.
pub fn contract_checked_ranked_weights(
    weights: &[[i128; 2]],
    source_edges: &[(usize, usize)],
    certificate: &RankedComponentCertificate,
) -> Result<RankedCountReceipt, Error> {
    // Always verify the exact certificate and edge list being consumed.
    // A receipt alone is not a reusable authority for different input bytes.
    let verified = verify_ranked_component_certificate(weights.len(), source_edges, certificate)?;
    let mut products = vec![[1i128, 1i128]; verified.components];
    checked_component_product_scan(&mut products, &certificate.labels, weights)?;
    let value = checked_component_product_finish(&products)?;
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RankedCountReceipt {
    pub value: i128,
    pub variable_count: usize,
    pub component_count: usize,
    pub checked_additions: usize,
    pub checked_multiplications: usize,
}
