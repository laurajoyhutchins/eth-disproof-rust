//! Exact contraction of unary Boolean weights with equality-only interactions.
//!
//! Unlike the disjoint matching representation, overlapping and cyclic
//! equality edges are supported. Union-find maintains a partition; contracting
//! one Boolean value per nonempty connected component is exact for *this*
//! factor language. No attempt is made to accept XOR, clauses, or arbitrary
//! cross-component factors.
//!
//! Inputs and intermediate values are checked i128. Capacity/overflow means
//! refusal, not modular arithmetic or an inferred exact result. Complexity:
//! union by size plus path compression has O((n + e) alpha(n)) amortized
//! build operations. Read-only root traversal during contraction has
//! O(n log n) worst-case parent hops from union by size.
//! Owned logical storage is O(n + e) machine words. This is an algorithmic
//! argument, not a certified Rust bit-level or peak-allocator bound.

use crate::Error;
use std::mem::size_of;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualityComponentRegion {
    unary: Vec<[i128; 2]>,
    parent: Vec<usize>,
    size: Vec<usize>,
    edges: Vec<(usize, usize)>,
    component_count: usize,
    successful_unions: usize,
    parent_hops_during_build: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EqualityComponentReceipt {
    pub value: i128,
    pub variable_count: usize,
    pub edge_count: usize,
    pub component_count: usize,
    pub successful_unions: usize,
    /// Actual parent traversals while constructing the partition.
    pub parent_hops_during_build: u64,
    /// Actual read-only parent traversals performed during contraction.
    pub parent_hops_during_contraction: u64,
    pub checked_additions: usize,
    pub checked_multiplications: usize,
    /// Bytes of logical Vec elements, including the n-component temporary,
    /// not an allocator-observed peak or upper bound on heap usage.
    pub logical_payload_bytes: usize,
}

impl EqualityComponentRegion {
    pub fn new(unary: Vec<[i128; 2]>) -> Self {
        let n = unary.len();
        Self {
            unary,
            parent: (0..n).collect(),
            size: vec![1; n],
            edges: Vec::new(),
            component_count: n,
            successful_unions: 0,
            parent_hops_during_build: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.unary.len()
    }

    pub fn is_empty(&self) -> bool {
        self.unary.is_empty()
    }

    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn component_count(&self) -> usize {
        self.component_count
    }

    /// Full compression with union by size. Build-time traversals are counted
    /// independently from evaluation traversals.
    fn find_compress(&mut self, x: usize) -> Result<usize, Error> {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
            self.parent_hops_during_build = self
                .parent_hops_during_build
                .checked_add(1)
                .ok_or(Error::Overflow)?;
        }
        let mut cursor = x;
        while self.parent[cursor] != cursor {
            let next = self.parent[cursor];
            self.parent[cursor] = root;
            cursor = next;
        }
        Ok(root)
    }

    fn find_readonly(&self, x: usize, hops: &mut u64) -> Result<usize, Error> {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
            *hops = hops.checked_add(1).ok_or(Error::Overflow)?;
        }
        Ok(root)
    }

    /// Add one equality interaction and close it transitively.
    ///
    /// Edges between already connected ports are harmless; self-equality is
    /// also a tautology. An invalid endpoint is refused before any mutation.
    pub fn apply_equality(&mut self, a: usize, b: usize) -> Result<(), Error> {
        if a >= self.len() || b >= self.len() {
            return Err(Error::Invalid(
                "equality port outside declared region".into(),
            ));
        }
        if self.edges.len() == usize::MAX {
            return Err(Error::Overflow);
        }
        // The counter can be bounded in advance: at most 2*(n-1) traversals
        // per find due to the finite parent forest, with checked accounting.
        let ra = self.find_compress(a)?;
        let rb = self.find_compress(b)?;
        if ra != rb {
            let (small, large) = if self.size[ra] <= self.size[rb] {
                (ra, rb)
            } else {
                (rb, ra)
            };
            self.parent[small] = large;
            self.size[large] = self.size[large]
                .checked_add(self.size[small])
                .ok_or(Error::Overflow)?;
            self.component_count -= 1;
            self.successful_unions += 1;
        }
        self.edges.push((a, b));
        Ok(())
    }

    /// Canonical contiguous component labels in first-vertex encounter order.
    ///
    /// Every output label is used by at least one vertex, matching the
    /// surjectivity premise of the Lean component-contraction theorem.
    /// This method is a *representation witness*, not a formally verified
    /// proof that the union-find parent forest matches all source edges.
    /// It uses O(n) temporary words and O(n log n) worst-case parent
    /// traversals with the current read-only lookup.
    pub fn component_labels(&self) -> Result<Vec<usize>, Error> {
        let n = self.len();
        let mut root_to_label = vec![usize::MAX; n];
        let mut labels = Vec::with_capacity(n);
        let mut next = 0usize;
        let mut hops = 0u64;
        for i in 0..n {
            let root = self.find_readonly(i, &mut hops)?;
            if root_to_label[root] == usize::MAX {
                root_to_label[root] = next;
                next = next.checked_add(1).ok_or(Error::Overflow)?;
            }
            labels.push(root_to_label[root]);
        }
        if next != self.component_count {
            return Err(Error::Invalid(
                "union-find component count disagrees with partition labels".into(),
            ));
        }
        Ok(labels)
    }

    /// Exact pointwise semantics; useful as an independent finite oracle.
    pub fn value_at(&self, assignment: &[bool]) -> Result<i128, Error> {
        if assignment.len() != self.len() {
            return Err(Error::Invalid("assignment width mismatch".into()));
        }
        if self
            .edges
            .iter()
            .any(|&(a, b)| assignment[a] != assignment[b])
        {
            return Ok(0);
        }
        assignment
            .iter()
            .enumerate()
            .try_fold(1i128, |value, (i, bit)| {
                value
                    .checked_mul(self.unary[i][usize::from(*bit)])
                    .ok_or(Error::Overflow)
            })
    }

    /// The unconstrained unary-product representation is retained only if
    /// no nontrivial interaction was introduced. Detecting degenerate
    /// cancellations or general equivalences is intentionally not attempted.
    pub fn as_unary_product_if_unconstrained(&self) -> Result<&[[i128; 2]], Error> {
        if self.successful_unions != 0 {
            return Err(Error::Capacity(
                "nontrivial equality interactions require component representation".into(),
            ));
        }
        Ok(&self.unary)
    }

    /// Component contraction with checked exact arithmetic.
    pub fn contract(&self) -> Result<EqualityComponentReceipt, Error> {
        let n = self.len();
        let mut factors = vec![[1i128, 1i128]; n];
        let mut hops = 0u64;
        let mut multiplications = 0usize;
        let mut additions = 0usize;
        for (i, weights) in self.unary.iter().enumerate() {
            let root = self.find_readonly(i, &mut hops)?;
            for (product, weight) in factors[root].iter_mut().zip(weights.iter()) {
                *product = product.checked_mul(*weight).ok_or(Error::Overflow)?;
                multiplications += 1;
            }
        }
        let mut result = 1i128;
        for (i, pair) in factors.iter().enumerate() {
            if self.parent[i] == i {
                let component_sum = pair[0].checked_add(pair[1]).ok_or(Error::Overflow)?;
                additions += 1;
                result = result.checked_mul(component_sum).ok_or(Error::Overflow)?;
                multiplications += 1;
            }
        }

        // Logical element bytes across both stored and temporary arrays.
        // Vec headers and allocator capacity/overhead are NOT included.
        let stored = n
            .checked_mul(size_of::<[i128; 2]>() + 2 * size_of::<usize>())
            .ok_or(Error::Overflow)?;
        let edges = self
            .edges
            .len()
            .checked_mul(size_of::<(usize, usize)>())
            .ok_or(Error::Overflow)?;
        let temporary = n
            .checked_mul(size_of::<[i128; 2]>())
            .ok_or(Error::Overflow)?;
        let logical_payload_bytes = stored
            .checked_add(edges)
            .and_then(|x| x.checked_add(temporary))
            .ok_or(Error::Overflow)?;

        Ok(EqualityComponentReceipt {
            value: result,
            variable_count: n,
            edge_count: self.edges.len(),
            component_count: self.component_count,
            successful_unions: self.successful_unions,
            parent_hops_during_build: self.parent_hops_during_build,
            parent_hops_during_contraction: hops,
            checked_additions: additions,
            checked_multiplications: multiplications,
            logical_payload_bytes,
        })
    }
}
