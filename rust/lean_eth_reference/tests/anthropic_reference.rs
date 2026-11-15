//! Independent bounded semantics oracle from Anthropic's MainResults.lean.
//!
//! Anthropic source: anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5
//! eth/MainResults.lean, blob 1c62a550fa1e4cbec65bb7112f92ad67589afddc
//!
//! This deliberately uses List (List (Fin n × Bool)) semantics, not this crate's
//! Finset representation, evaluation method or enumerating leaf, to derive
//! expected finite counts. It is NOT an Anthropic TM2 interpreter, a formal
//! equivalence theorem, or evidence of subexponential running time.

use lean_eth_reference::{Cnf, EnumeratingLeaf, Limits, count_cnf};

/// Unnormalized Anthropic CNF: literals and clauses remain ordered lists,
/// including repeated literals or equivalent clauses in different orders.
#[derive(Clone, Debug)]
struct ReferenceCnf {
    n: usize,
    clauses: Vec<Vec<(usize, bool)>>,
}

impl ReferenceCnf {
    fn satisfies(&self, mask: u128) -> bool {
        assert!(self.n <= 8, "bounded external oracle");
        self.clauses.iter().all(|clause| {
            clause
                .iter()
                .any(|(i, positive)| (((mask >> i) & 1) == 1) == *positive)
        })
    }

    fn num_sat(&self) -> u128 {
        assert!(self.n <= 8, "bounded external oracle");
        (0..(1_u128 << self.n))
            .filter(|assignment| self.satisfies(*assignment))
            .count() as u128
    }

    /// Anthropic's `binary n c`: exactly n+1 lowest bits, LSB first.
    fn binary(&self, count: u128) -> Vec<bool> {
        (0..=self.n).map(|i| (count >> i) & 1 == 1).collect()
    }

    /// Anthropic's `encInput`: unary k, unary n, then k fixed-width slots
    /// for each clause, little-endian. Not the OpenAI Finset bit encoding.
    fn enc_input(&self, k: usize) -> Vec<bool> {
        assert!(self.clauses.iter().all(|c| c.len() <= k));
        let mut out = Vec::new();
        out.extend(std::iter::repeat_n(true, k));
        out.push(false);
        out.extend(std::iter::repeat_n(true, self.n));
        out.push(false);
        // Nat.log2 (2*n) + 1; for n=0, Nat.log2 0 = 0.
        let twice_n = 2 * self.n;
        let width = if twice_n == 0 {
            1
        } else {
            (usize::BITS - twice_n.leading_zeros()) as usize
        };
        for clause in &self.clauses {
            for j in 0..k {
                let slot = clause
                    .get(j)
                    .map_or(0, |(i, positive)| 2 * i + 1 + usize::from(*positive));
                out.extend((0..width).map(|b| (slot >> b) & 1 == 1));
            }
        }
        out
    }

    /// Only for cross-model comparison. This conversion deliberately drops
    /// order and multiplicity, which cannot change OR/AND satisfaction.
    fn as_openai_finset(&self) -> Cnf {
        let rows: Vec<Vec<i64>> = self
            .clauses
            .iter()
            .map(|row| {
                row.iter()
                    .map(|(i, positive)| {
                        assert!(*i < self.n);
                        let dimacs = (i + 1) as i64;
                        if *positive { dimacs } else { -dimacs }
                    })
                    .collect()
            })
            .collect();
        let slices: Vec<&[i64]> = rows.iter().map(Vec::as_slice).collect();
        Cnf::from_signed(self.n, &slices).unwrap()
    }
}

#[test]
fn anthro_mainresults_valid_case_has_nine_models_and_expected_word() {
    // n>=4, two distinct clauses, every variable occurs, k=2.
    // (x0 OR not x1) AND (x2 OR x3): 3*3 = 9 models.
    let f = ReferenceCnf {
        n: 4,
        clauses: vec![vec![(0, true), (1, false)], vec![(2, true), (3, true)]],
    };
    assert_eq!(f.num_sat(), 9);
    assert_eq!(f.binary(9), vec![true, false, false, true, false]);

    // Explicit known encoding, derived from the source's slot and unary
    // definitions, to catch polarity, index, width and endian reversals.
    // k prefix 110; n prefix 11110;
    // slots: +x0=2 (0100), -x1=3 (1100), +x2=6 (0110), +x3=8 (0001).
    let word: String = f
        .enc_input(2)
        .iter()
        .map(|bit| if *bit { '1' } else { '0' })
        .collect();
    assert_eq!(word, "110111100100110001100001");
    assert_ne!(word, f.as_openai_finset().encode_lean());
}

#[test]
fn anthro_list_semantics_and_openai_finset_semantics_agree_on_edge_cases() {
    let cases = [
        ReferenceCnf {
            n: 0,
            clauses: vec![],
        },
        ReferenceCnf {
            n: 3,
            clauses: vec![],
        },
        ReferenceCnf {
            n: 3,
            clauses: vec![vec![]],
        },
        ReferenceCnf {
            n: 3,
            clauses: vec![vec![(0, true), (0, false)]],
        },
        ReferenceCnf {
            n: 3,
            clauses: vec![vec![(0, false)]],
        },
        ReferenceCnf {
            n: 4,
            clauses: vec![vec![(0, true), (0, true), (1, false)]],
        },
        ReferenceCnf {
            n: 4,
            clauses: vec![vec![(0, true)], vec![(0, true)]],
        },
        ReferenceCnf {
            n: 4,
            clauses: vec![vec![(1, false), (0, true)], vec![(0, true), (1, false)]],
        },
        ReferenceCnf {
            n: 5,
            clauses: vec![
                vec![(0, true), (1, false)],
                vec![(2, true)],
                vec![(4, false)],
            ],
        },
        ReferenceCnf {
            n: 5,
            clauses: vec![vec![(0, true)], vec![(0, false)]],
        },
    ];
    for case in cases {
        let openai = case.as_openai_finset();
        let mut openai_count = 0_u128;
        for mask in 0..(1_u128 << case.n) {
            assert_eq!(
                case.satisfies(mask),
                openai.eval_mask_checked(mask).unwrap(),
                "assignment {mask}, formula {case:?}"
            );
            if openai.eval_mask_checked(mask).unwrap() {
                openai_count += 1;
            }
        }
        assert_eq!(case.num_sat(), openai_count, "{case:?}");
        let bit_count = case.binary(case.num_sat());
        assert_eq!(bit_count.len(), case.n + 1);
        let reconstructed = bit_count
            .iter()
            .enumerate()
            .fold(0_u128, |acc, (i, b)| acc | (u128::from(*b) << i));
        assert_eq!(reconstructed, case.num_sat());
    }
}

#[test]
fn semantic_sparsification_reference_agrees_with_independent_counts() {
    // These two explicit models are not an Anthropic machine run. They check
    // our existing bounded semantic program against the independent meaning.
    let cases = [
        ReferenceCnf {
            n: 4,
            clauses: vec![vec![(0, true), (1, false)], vec![(2, true), (3, true)]],
        },
        ReferenceCnf {
            n: 4,
            clauses: vec![vec![(0, true)], vec![(0, false)], vec![(2, true)]],
        },
    ];
    for f in cases {
        let expected = f.num_sat();
        let (got, _) = count_cnf(
            f.as_openai_finset(),
            2,
            &mut EnumeratingLeaf { max_variables: 8 },
            Limits {
                max_nodes: 1000,
                max_candidates_per_node: 10000,
                max_depth: 40,
                max_leaf_variables: 8,
            },
        )
        .unwrap();
        assert_eq!(got, expected, "{f:?}");
    }
}

#[test]
fn anthro_output_preserves_the_highest_possible_count_bit() {
    // The all-satisfying empty formula has 2^n models, requiring n+1 bits.
    let f = ReferenceCnf {
        n: 4,
        clauses: vec![],
    };
    assert_eq!(f.num_sat(), 16);
    assert_eq!(
        f.binary(f.num_sat()),
        vec![false, false, false, false, true]
    );
}
