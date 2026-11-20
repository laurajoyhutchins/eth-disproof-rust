use crate::Arithmetic;
use egg::{Id, RecExpr};
use num_bigint::BigInt;
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Node {
    Number(i64),
    Variable(String),
    Add(usize, usize),
    Mul(usize, usize),
    Pair(usize, usize),
}

#[derive(Clone, Debug)]
pub struct Plan {
    pub(crate) nodes: Vec<Node>,
    pub(crate) outputs: [usize; 2],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluation {
    pub outputs: [BigInt; 2],
    pub additions: usize,
    pub multiplications: usize,
    // A workload proxy, not a bit-complexity theorem or a wall-time estimate.
    pub operand_byte_work_proxy: u128,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Polynomial {
    terms: BTreeMap<Vec<String>, BigInt>,
}

impl Polynomial {
    fn add_term(&mut self, key: Vec<String>, coefficient: BigInt) {
        let sum = self.terms.remove(&key).unwrap_or_default() + coefficient;
        if sum != BigInt::from(0) {
            self.terms.insert(key, sum);
        }
    }

    fn multiply(&self, other: &Self) -> Result<Self, String> {
        let pairs = self.terms.len().checked_mul(other.terms.len()).unwrap_or(usize::MAX);
        if pairs > 40_000 {
            return Err("polynomial product-pair budget exceeded".into());
        }
        let mut out = Self::default();
        for (a, ac) in &self.terms {
            for (b, bc) in &other.terms {
                let mut m = a.clone();
                m.extend(b.iter().cloned());
                m.sort_unstable();
                out.add_term(m, ac * bc);
                if out.terms.len() > 4_096 {
                    return Err("polynomial term budget exceeded".into());
                }
            }
        }
        Ok(out)
    }
}

impl Plan {
    // The original baseline gets structural hash-consing too. We do not
    // compare an optimized DAG against an artificially duplicated input tree.
    pub(crate) fn from_expr(expr: &RecExpr<Arithmetic>) -> Result<Self, String> {
        let mut nodes = Vec::new();
        let mut intern = HashMap::<Node, usize>::new();
        let mut source_ids = Vec::<usize>::new();
        for op in expr.as_ref() {
            let get = |id: Id| source_ids[usize::from(id)];
            let node = match op {
                Arithmetic::Number(n) => Node::Number(*n),
                Arithmetic::Variable(s) => Node::Variable(s.to_string()),
                Arithmetic::Add([a, b]) => Node::Add(get(*a), get(*b)),
                Arithmetic::Mul([a, b]) => Node::Mul(get(*a), get(*b)),
                Arithmetic::Pair([a, b]) => Node::Pair(get(*a), get(*b)),
            };
            let id = if let Some(id) = intern.get(&node) {
                *id
            } else {
                let id = nodes.len();
                nodes.push(node.clone());
                intern.insert(node, id);
                id
            };
            source_ids.push(id);
        }
        let root = *source_ids.last().ok_or("empty expression")?;
        let outputs = match nodes[root] {
            Node::Pair(a, b) => [a, b],
            _ => return Err("expected two-output (pair ... ...) root".into()),
        };
        Ok(Self { nodes, outputs })
    }

    pub fn operation_count(&self) -> usize {
        self.nodes.iter().filter(|n| matches!(n, Node::Add(..) | Node::Mul(..))).count()
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn evaluate(&self, bindings: &BTreeMap<String, BigInt>) -> Result<Evaluation, String> {
        let mut v: Vec<BigInt> = Vec::with_capacity(self.nodes.len());
        let (mut additions, mut multiplications, mut proxy) = (0, 0, 0_u128);
        for node in &self.nodes {
            let val = match node {
                Node::Number(n) => BigInt::from(*n),
                Node::Variable(s) => bindings.get(s).cloned().ok_or_else(|| format!("unbound variable {s}"))?,
                Node::Add(a, b) => {
                    additions += 1;
                    proxy += v[*a].to_signed_bytes_le().len().max(v[*b].to_signed_bytes_le().len()) as u128;
                    &v[*a] + &v[*b]
                }
                Node::Mul(a, b) => {
                    multiplications += 1;
                    proxy += (v[*a].to_signed_bytes_le().len() as u128)
                        * (v[*b].to_signed_bytes_le().len() as u128);
                    &v[*a] * &v[*b]
                }
                Node::Pair(_, _) => BigInt::from(0),
            };
            v.push(val);
        }
        Ok(Evaluation {
            outputs: [v[self.outputs[0]].clone(), v[self.outputs[1]].clone()],
            additions,
            multiplications,
            operand_byte_work_proxy: proxy,
        })
    }

    // Independent normal form over Z[variables]. All monomials are sorted.
    // Resource limits refuse equivalence instead of silently dropping terms.
    pub(crate) fn polynomials(&self) -> Result<[Polynomial; 2], String> {
        let mut polys: Vec<Polynomial> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let poly = match node {
                Node::Number(n) => {
                    let mut p = Polynomial::default();
                    p.add_term(vec![], BigInt::from(*n));
                    p
                }
                Node::Variable(s) => {
                    let mut p = Polynomial::default();
                    p.add_term(vec![s.clone()], BigInt::from(1));
                    p
                }
                Node::Add(a, b) => {
                    let mut p = polys[*a].clone();
                    for (m, c) in &polys[*b].terms {
                        p.add_term(m.clone(), c.clone());
                    }
                    p
                }
                Node::Mul(a, b) => polys[*a].multiply(&polys[*b])?,
                Node::Pair(_, _) => Polynomial::default(),
            };
            if poly.terms.len() > 4_096 {
                return Err("polynomial term budget exceeded".into());
            }
            polys.push(poly);
        }
        Ok([polys[self.outputs[0]].clone(), polys[self.outputs[1]].clone()])
    }
}

/// Valid for pure, commutative integer polynomials. Not a Lean kernel proof.
pub fn exact_polynomial_equivalent(a: &Plan, b: &Plan) -> Result<bool, String> {
    Ok(a.polynomials()? == b.polynomials()?)
}
