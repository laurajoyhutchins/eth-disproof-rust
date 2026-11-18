//! Independent, linear-time verifier for an equality-component certificate.
//!
//! The verifier intentionally does NOT call production union-find and does
//! NOT trust its root pointers, ranks, or component count. It checks that:
//! * all claimed class labels are in [0, c) and every class is populated;
//! * every original equality edge stays inside its claimed class;
//! * the referenced original edges form a spanning forest within each class.
//!
//! Thus claimed label equality iff source-edge reachability. The mathematical
//! sufficiency of these conditions is proved in ACC.EqualityCertificate.
//! This Rust checker itself is not formally refined to Lean.

use crate::Error;

/// Reusable, source-bound witness; forest indices point into the *original*
/// equality-edge list, not into internal parent pointers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentCertificate {
    pub labels: Vec<usize>,
    pub forest_edge_indices: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedComponentCertificate {
    pub variables: usize,
    pub original_edges: usize,
    pub components: usize,
    pub forest_edges: usize,
}

/// Check the certificate with independent adjacency traversal, not DSU.
///
/// O(n+e) word operations/space, excluding allocator overhead and byte costs.
/// The caller must supply the actual source edge list whose semantics are to
/// be certified; checking a different edge list certifies a different graph.
pub fn verify_component_certificate(
    variable_count: usize,
    source_edges: &[(usize, usize)],
    certificate: &ComponentCertificate,
) -> Result<VerifiedComponentCertificate, Error> {
    let n = variable_count;
    if certificate.labels.len() != n {
        return Err(Error::Invalid("certificate label width mismatch".into()));
    }
    for &(a, b) in source_edges {
        if a >= n || b >= n {
            return Err(Error::Invalid("source edge outside declared width".into()));
        }
    }
    let mut component_count = 0usize;
    for &label in &certificate.labels {
        if label >= n {
            return Err(Error::Invalid("component label outside dense range".into()));
        }
        component_count = component_count.max(label + 1);
    }
    let mut label_seen = vec![false; component_count];
    for &label in &certificate.labels {
        label_seen[label] = true;
    }
    if label_seen.iter().any(|seen| !seen) {
        return Err(Error::Invalid("unused component label".into()));
    }

    for &(a, b) in source_edges {
        if certificate.labels[a] != certificate.labels[b] {
            return Err(Error::Invalid(
                "source edge crosses claimed components".into(),
            ));
        }
    }

    if certificate.forest_edge_indices.len() != n - component_count {
        return Err(Error::Invalid("spanning forest edge count mismatch".into()));
    }
    let mut used_source_edge = vec![false; source_edges.len()];
    let mut adjacency = vec![Vec::<usize>::new(); n];
    for &edge_index in &certificate.forest_edge_indices {
        let &(a, b) = source_edges
            .get(edge_index)
            .ok_or_else(|| Error::Invalid("forest references nonexistent source edge".into()))?;
        if used_source_edge[edge_index] {
            return Err(Error::Invalid("duplicate forest edge reference".into()));
        }
        used_source_edge[edge_index] = true;
        if a == b || certificate.labels[a] != certificate.labels[b] {
            return Err(Error::Invalid(
                "forest edge is not an internal tree link".into(),
            ));
        }
        adjacency[a].push(b);
        adjacency[b].push(a);
    }

    // Independent traversal of certified forest edges. If the same label
    // occurs in two distinct forest components, the alleged forest is
    // incomplete and the certificate is rejected.
    let mut visited = vec![false; n];
    let mut visited_labels = vec![false; component_count];
    let mut stack = Vec::new();
    for start in 0..n {
        if visited[start] {
            continue;
        }
        let label = certificate.labels[start];
        if visited_labels[label] {
            return Err(Error::Invalid(
                "equal-labeled vertices lack a certified forest path".into(),
            ));
        }
        visited_labels[label] = true;
        visited[start] = true;
        stack.push(start);
        while let Some(vertex) = stack.pop() {
            for &next in &adjacency[vertex] {
                if certificate.labels[next] != label {
                    return Err(Error::Invalid("forest path crosses claimed label".into()));
                }
                if !visited[next] {
                    visited[next] = true;
                    stack.push(next);
                }
            }
        }
    }

    Ok(VerifiedComponentCertificate {
        variables: n,
        original_edges: source_edges.len(),
        components: component_count,
        forest_edges: certificate.forest_edge_indices.len(),
    })
}
