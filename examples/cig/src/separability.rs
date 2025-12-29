//! Separability testing for Boolean functions.
//!
//! A Boolean function f is separable over partition (A, B) if there exist
//! functions g (on A) and h (on B) and binary operator ⊗ such that:
//!
//! ```text
//! f(x) = g(x_A) ⊗ h(x_B)
//! ```
//!
//! This module provides algorithms for testing separability and finding
//! the interaction partition.

use crate::partition::Partition;
use crate::truth_table::TruthTable;
use crate::variable::{Var, VarSet};

/// The binary operators considered for separability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    /// Conjunction (AND): a ∧ b
    And,
    /// Disjunction (OR): a ∨ b
    Or,
    /// Exclusive-or (XOR): a ⊕ b
    Xor,
}

impl Operator {
    /// Apply the operator to two Boolean values.
    pub fn apply(self, a: bool, b: bool) -> bool {
        match self {
            Operator::And => a && b,
            Operator::Or => a || b,
            Operator::Xor => a ^ b,
        }
    }

    /// Apply the operator to a list of Boolean values.
    pub fn apply_all(self, inputs: &[bool]) -> bool {
        match self {
            Operator::And => inputs.iter().all(|&b| b),
            Operator::Or => inputs.iter().any(|&b| b),
            Operator::Xor => inputs.iter().fold(false, |acc, &b| acc ^ b),
        }
    }

    /// Get the symbol for this operator.
    pub fn symbol(self) -> &'static str {
        match self {
            Operator::And => "∧",
            Operator::Or => "∨",
            Operator::Xor => "⊕",
        }
    }

    /// All operators in the canonical order.
    pub fn all() -> [Operator; 3] {
        [Operator::And, Operator::Or, Operator::Xor]
    }
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.symbol())
    }
}

/// Result of a separability test.
#[derive(Debug, Clone)]
pub struct SeparabilityResult {
    /// Whether the function is separable.
    pub is_separable: bool,
    /// If separable, the operator used.
    pub operator: Option<Operator>,
    /// If separable, the function g on block A.
    pub g: Option<TruthTable>,
    /// If separable, the function h on block B.
    pub h: Option<TruthTable>,
}

impl SeparabilityResult {
    fn not_separable() -> Self {
        SeparabilityResult {
            is_separable: false,
            operator: None,
            g: None,
            h: None,
        }
    }

    fn separable(op: Operator, g: TruthTable, h: TruthTable) -> Self {
        SeparabilityResult {
            is_separable: true,
            operator: Some(op),
            g: Some(g),
            h: Some(h),
        }
    }
}

/// Build the characteristic matrix for a function and partition.
///
/// For f with partition (A, B), the matrix M[i,j] = f(α_i, β_j)
/// where α_i is the i-th assignment to A and β_j is the j-th to B.
pub fn characteristic_matrix(f: &TruthTable, a_vars: &VarSet, b_vars: &VarSet) -> Vec<Vec<bool>> {
    let a_list: Vec<Var> = a_vars.iter().collect();
    let b_list: Vec<Var> = b_vars.iter().collect();

    let a_size = 1usize << a_list.len();
    let b_size = 1usize << b_list.len();

    let n = f.num_vars() as usize;
    let mut matrix = vec![vec![false; b_size]; a_size];
    let mut assignment = vec![false; n];

    for i in 0..a_size {
        for j in 0..b_size {
            // Set assignment for A variables
            for (k, &var) in a_list.iter().enumerate() {
                assignment[var.position()] = (i >> k) & 1 == 1;
            }
            // Set assignment for B variables
            for (k, &var) in b_list.iter().enumerate() {
                assignment[var.position()] = (j >> k) & 1 == 1;
            }
            matrix[i][j] = f.eval(&assignment);
        }
    }

    matrix
}

/// Check if a matrix has rank 1 for AND operation.
///
/// M has AND-rank 1 iff M[i,j] = u[i] ∧ v[j] for some vectors u, v.
fn has_and_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();
    let cols = matrix[0].len();

    // For AND-rank 1:
    // If M[i,j] = u[i] ∧ v[j]:
    // - If any M[i,j] = 1, then u[i] = 1 and v[j] = 1
    // - Row i is all zeros iff u[i] = 0
    // - Column j is all zeros iff v[j] = 0

    // Find a row that's not all zeros (if any)
    let mut u = vec![false; rows];
    let mut v = vec![false; cols];

    // First pass: mark rows/cols that must be 1
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if val {
                u[i] = true;
                v[j] = true;
            }
        }
    }

    // Verify: if u[i] = 1 and v[j] = 1, then M[i,j] must be 1
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if u[i] && v[j] && !val {
                return None;
            }
        }
    }

    Some((u, v))
}

/// Check if a matrix has rank 1 for OR operation.
///
/// M has OR-rank 1 iff M[i,j] = u[i] ∨ v[j] for some vectors u, v.
fn has_or_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();
    let cols = matrix[0].len();

    // For OR-rank 1:
    // If M[i,j] = u[i] ∨ v[j]:
    // - If any M[i,j] = 0, then u[i] = 0 and v[j] = 0
    // - Row i is all ones iff u[i] = 1
    // - Column j is all ones iff v[j] = 1

    let mut u = vec![true; rows]; // Start with all 1s
    let mut v = vec![true; cols];

    // First pass: mark rows/cols that must be 0
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if !val {
                u[i] = false;
                v[j] = false;
            }
        }
    }

    // Verify: if u[i] = 0 and v[j] = 0, then M[i,j] must be 0
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if !u[i] && !v[j] && val {
                return None;
            }
        }
    }

    Some((u, v))
}

/// Check if a matrix has rank 1 for XOR operation (over GF(2)).
///
/// M has XOR-rank 1 iff M[i,j] = u[i] ⊕ v[j] for some vectors u, v.
fn has_xor_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();

    // For XOR-rank 1:
    // If M[i,j] = u[i] ⊕ v[j], then:
    // - M[i,j] ⊕ M[i,k] = v[j] ⊕ v[k] (independent of i)
    // - M[i,j] ⊕ M[k,j] = u[i] ⊕ u[k] (independent of j)

    // Strategy: Fix u[0] = 0 (WLOG), deduce v from row 0
    // Then verify all other rows are consistent

    let mut u = vec![false; rows];
    let v: Vec<bool> = matrix[0].clone();

    // Deduce u from column 0
    for (i, row) in matrix.iter().enumerate() {
        u[i] = row[0] ^ v[0];
    }

    // Verify all entries
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if (u[i] ^ v[j]) != val {
                return None;
            }
        }
    }

    Some((u, v))
}

/// Test if a function is separable over a given partition.
pub fn test_separability(f: &TruthTable, a_vars: &VarSet, b_vars: &VarSet) -> SeparabilityResult {
    // Handle edge cases
    if a_vars.is_empty() || b_vars.is_empty() {
        return SeparabilityResult::not_separable();
    }

    let matrix = characteristic_matrix(f, a_vars, b_vars);

    // Try each operator
    for op in Operator::all() {
        let result = match op {
            Operator::And => has_and_rank_1(&matrix),
            Operator::Or => has_or_rank_1(&matrix),
            Operator::Xor => has_xor_rank_1(&matrix),
        };

        if let Some((u, v)) = result {
            // Construct the subfunctions
            let g = truth_table_from_vector(&u, a_vars.len() as u32);
            let h = truth_table_from_vector(&v, b_vars.len() as u32);
            return SeparabilityResult::separable(op, g, h);
        }
    }

    SeparabilityResult::not_separable()
}

/// Convert a Boolean vector to a truth table.
fn truth_table_from_vector(v: &[bool], n: u32) -> TruthTable {
    TruthTable::from_expr(n, |x| {
        let idx = x.iter().enumerate().fold(0usize, |acc, (i, &b)| acc | ((b as usize) << i));
        v.get(idx).copied().unwrap_or(false)
    })
}

/// Find the interaction partition of a function.
///
/// Returns the unique coarsest partition such that the function is
/// separable over any split of distinct blocks.
pub fn find_interaction_partition(f: &TruthTable) -> Partition {
    let vars = f.essential_vars();

    if vars.len() <= 1 {
        return Partition::discrete(&vars);
    }

    // Start with the discrete partition
    let mut blocks: Vec<VarSet> = vars.iter().map(VarSet::singleton).collect();

    // Iteratively merge blocks that must interact
    let mut changed = true;
    while changed {
        changed = false;

        'outer: for i in 0..blocks.len() {
            for j in (i + 1)..blocks.len() {
                let a = &blocks[i];
                let b = &blocks[j];

                // Test if these blocks interact in the original function
                if sets_interact(f, a, b) {
                    // Must merge these blocks
                    let merged = blocks[i].union(&blocks[j]);
                    blocks.remove(j);
                    blocks[i] = merged;
                    changed = true;
                    break 'outer;
                }
            }
        }
    }

    Partition::from_blocks(blocks)
}

/// Restrict a function to a subset of its variables.
/// This creates a new function that only depends on the given variables,
/// by fixing all other variables to 0.
#[allow(dead_code)]
fn restrict_to_vars(f: &TruthTable, vars: &VarSet) -> TruthTable {
    let var_list: Vec<Var> = vars.iter().collect();
    let new_n = var_list.len() as u32;

    TruthTable::from_expr(new_n, |x| {
        // Map new indices to old
        let mut full_assignment = vec![false; f.num_vars() as usize];
        for (new_idx, &var) in var_list.iter().enumerate() {
            full_assignment[var.position()] = x[new_idx];
        }
        f.eval(&full_assignment)
    })
}

/// Check if two variable sets interact in a function.
///
/// Two sets A and B interact if there's no operator ⊗ such that
/// f(x) = g(x_A) ⊗ h(x_B) for all assignments to other variables.
///
/// We test this by checking if for ALL cofactors (fixing other variables),
/// A and B remain separable with the SAME operator.
fn sets_interact(f: &TruthTable, a_vars: &VarSet, b_vars: &VarSet) -> bool {
    let all_vars = f.essential_vars();
    let other_vars: Vec<Var> = all_vars.iter().filter(|v| !a_vars.contains(*v) && !b_vars.contains(*v)).collect();

    if other_vars.is_empty() {
        // No other variables - just test directly
        let result = test_separability(f, a_vars, b_vars);
        return !result.is_separable;
    }

    // Test all cofactors
    let num_others = other_vars.len();
    let mut common_operator: Option<Operator> = None;

    for assignment in 0..(1usize << num_others) {
        // Create cofactor
        let cofactor = create_cofactor(f, &other_vars, assignment);

        // Build variable mapping for the cofactor
        let a_and_b: VarSet = a_vars.union(b_vars);
        let var_list: Vec<Var> = a_and_b.iter().collect();

        let a_new: VarSet = var_list
            .iter()
            .enumerate()
            .filter(|(_, v)| a_vars.contains(**v))
            .map(|(i, _)| Var::new((i + 1) as u32))
            .collect();

        let b_new: VarSet = var_list
            .iter()
            .enumerate()
            .filter(|(_, v)| b_vars.contains(**v))
            .map(|(i, _)| Var::new((i + 1) as u32))
            .collect();

        let result = test_separability(&cofactor, &a_new, &b_new);

        if !result.is_separable {
            return true; // They interact
        }

        // Check operator consistency
        let op = result.operator.unwrap();
        match common_operator {
            None => common_operator = Some(op),
            Some(prev) if prev != op => return true, // Different operators means interaction
            _ => {}
        }
    }

    false // All cofactors separable with same operator
}

/// Create a cofactor by fixing some variables.
fn create_cofactor(f: &TruthTable, vars_to_fix: &[Var], assignment: usize) -> TruthTable {
    let remaining_vars: Vec<Var> = (1..=f.num_vars()).map(Var::new).filter(|v| !vars_to_fix.contains(v)).collect();

    let new_n = remaining_vars.len() as u32;

    TruthTable::from_expr(new_n, |x| {
        let mut full_assignment = vec![false; f.num_vars() as usize];

        // Set fixed variables
        for (i, var) in vars_to_fix.iter().enumerate() {
            full_assignment[var.position()] = (assignment >> i) & 1 == 1;
        }

        // Set remaining variables
        for (i, var) in remaining_vars.iter().enumerate() {
            full_assignment[var.position()] = x[i];
        }

        f.eval(&full_assignment)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::truth_table::named;

    #[test]
    fn test_and_separability_partition() {
        // x₁ ∧ x₂ is separable: can be factored as x₁ ∧ x₂
        // Therefore x₁ and x₂ do NOT interact (can be in different blocks).
        let f = TruthTable::from_expr(2, |x| x[0] && x[1]);
        let x1 = VarSet::singleton(Var(1));
        let x2 = VarSet::singleton(Var(2));

        // They do NOT interact (separable partition exists)
        assert!(!sets_interact(&f, &x1, &x2));

        // Interaction partition has 2 blocks
        let ip = find_interaction_partition(&f);
        assert_eq!(ip.num_blocks(), 2, "Separable function should have multiple blocks");
    }

    #[test]
    fn test_xor_separability() {
        // x₁ ⊕ x₂ is separable via XOR
        let f = TruthTable::from_expr(2, |x| x[0] ^ x[1]);
        let a = VarSet::singleton(Var(1));
        let b = VarSet::singleton(Var(2));

        let result = test_separability(&f, &a, &b);
        assert!(result.is_separable);
        assert_eq!(result.operator, Some(Operator::Xor));
    }

    #[test]
    fn test_mux_not_separable() {
        // MUX(s, x, y) = (s ∧ x) ∨ (¬s ∧ y) is not separable over any 2-1 partition
        let f = named::mux();

        // Test all 2-1 partitions
        let vars = VarSet::from_iter([Var(1), Var(2), Var(3)]);
        for (a, b) in Partition::two_partitions(&vars) {
            if a.len() == 1 && b.len() == 2 {
                // MUX should have all variables interact
                assert!(sets_interact(&f, &a, &b), "MUX should have interacting variables");
            }
        }
    }

    #[test]
    fn test_interaction_partition_xor() {
        // f = x₁ ⊕ x₂ ⊕ x₃ should be fully separable
        let f = named::xor_all(3);
        let ip = find_interaction_partition(&f);

        // Each variable should be in its own block
        assert_eq!(ip.num_blocks(), 3);
    }

    #[test]
    fn test_interaction_partition_maj() {
        // MAJ₃ is not separable
        let f = named::majority3();
        let ip = find_interaction_partition(&f);

        // All variables should be in one block
        assert_eq!(ip.num_blocks(), 1);
    }

    #[test]
    fn test_interaction_partition_composed() {
        // f = (x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄)
        let f = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] ^ x[3]));
        let ip = find_interaction_partition(&f);

        // This function is separable as g(x₁, x₂) ∧ h(x₃, x₄)
        // where g = x₁ ⊕ x₂ and h = x₃ ⊕ x₄
        //
        // Within each subfunction:
        // - x₁ and x₂ interact (because XOR is not constant across all cofactors of the other)
        // - x₃ and x₄ interact similarly
        //
        // So the interaction partition should be {{x₁, x₂}, {x₃, x₄}}
        assert_eq!(ip.num_blocks(), 2);

        // Verify the blocks contain the right variables
        let blocks = ip.blocks();
        let block1_vars: Vec<u32> = blocks[0].iter().map(|v| v.index()).collect();
        let block2_vars: Vec<u32> = blocks[1].iter().map(|v| v.index()).collect();

        // One block should have {1, 2} and the other {3, 4}
        let has_12 = (block1_vars == vec![1, 2]) || (block2_vars == vec![1, 2]);
        let has_34 = (block1_vars == vec![3, 4]) || (block2_vars == vec![3, 4]);
        assert!(has_12 && has_34, "Blocks should be {{1,2}} and {{3,4}}");
    }
}
