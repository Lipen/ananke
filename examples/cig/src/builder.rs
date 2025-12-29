//! CIG builder: constructs CIG from Boolean functions.
//!
//! The builder analyzes the separability structure of a Boolean function
//! and constructs the canonical interaction graph.

use std::sync::Arc;

use crate::cig::{Cig, CigNode, CigNodeKind, UniqueTable};
use crate::interaction::InteractionFunction;
use crate::partition::Partition;
use crate::separability::{find_interaction_partition, Operator};
use crate::truth_table::TruthTable;
use crate::variable::{Var, VarSet};

/// Builder for constructing CIGs from Boolean functions.
pub struct CigBuilder {
    /// Unique table for hash-consing nodes.
    unique_table: UniqueTable,
}

impl Default for CigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl CigBuilder {
    /// Create a new CIG builder.
    pub fn new() -> Self {
        CigBuilder {
            unique_table: UniqueTable::new(),
        }
    }

    /// Build a CIG from a truth table.
    pub fn build(&mut self, f: &TruthTable) -> Cig {
        let root = self.build_recursive(f);
        Cig::new(root)
    }

    /// Build a CIG node recursively.
    fn build_recursive(&mut self, f: &TruthTable) -> Arc<CigNode> {
        // Handle constant functions
        if f.is_zero() {
            return self.unique_table.zero();
        }
        if f.is_one() {
            return self.unique_table.one();
        }

        // Get essential variables
        let vars = f.essential_vars();

        // Single variable: return leaf
        if vars.len() == 1 {
            let var = vars.iter().next().unwrap();
            // Check if it's the variable or its negation
            let mut assignment = vec![false; f.num_vars() as usize];
            assignment[var.position()] = true;
            if f.eval(&assignment) {
                return self.unique_table.leaf(var);
            } else {
                // Negated variable: represented as internal node with negation
                let leaf = self.unique_table.leaf(var);
                let neg_interaction = InteractionFunction::from_expr(1, |x| !x[0]);
                return self.unique_table.internal(neg_interaction, vec![leaf]);
            }
        }

        // Find the interaction partition
        let partition = find_interaction_partition(f);

        if partition.num_blocks() == 1 {
            // Fully irreducible: all variables interact
            return self.build_irreducible(f, &vars);
        }

        // Separable: build with flattening for canonicity
        self.build_separable(f, &partition)
    }

    /// Build a node for an irreducible function.
    fn build_irreducible(&mut self, f: &TruthTable, vars: &VarSet) -> Arc<CigNode> {
        // For an irreducible function, we create an internal node
        // with children being the variables, and the interaction
        // function being the function itself.

        let var_list: Vec<Var> = vars.iter().collect();
        let children: Vec<Arc<CigNode>> = var_list.iter().map(|&v| self.unique_table.leaf(v)).collect();

        // The interaction function is f itself (reindexed)
        let n = var_list.len() as u32;
        let interaction = InteractionFunction::from_expr(n, |x| {
            // Map x to full assignment
            let mut full = vec![false; f.num_vars() as usize];
            for (i, &var) in var_list.iter().enumerate() {
                full[var.position()] = x[i];
            }
            f.eval(&full)
        });

        // Sort children by variable index for canonicity
        let mut indexed_children: Vec<_> = children.into_iter().enumerate().map(|(i, c)| (var_list[i], c)).collect();
        indexed_children.sort_by_key(|(v, _)| v.index());

        let sorted_children: Vec<_> = indexed_children.into_iter().map(|(_, c)| c).collect();

        self.unique_table.internal(interaction, sorted_children)
    }

    /// Build a node for a separable function with proper n-ary flattening.
    ///
    /// This ensures canonicity by:
    /// 1. Finding the separating operator between blocks
    /// 2. Recursively building children
    /// 3. Flattening any children that use the same operator
    /// 4. Sorting all children by canonical hash
    fn build_separable(&mut self, f: &TruthTable, partition: &Partition) -> Arc<CigNode> {
        let blocks = partition.blocks();

        // For 2+ blocks, we need to find the separating operator
        // We test separation between first block and rest
        let first = &blocks[0];
        let rest_vars: VarSet = blocks[1..].iter().fold(VarSet::empty(), |acc, b| acc.union(b));

        let result = test_separability_on_function(f, first, &rest_vars);
        if !result.is_separable {
            panic!("Expected separable function but separability test failed");
        }

        let op = result.operator.unwrap();
        let g = result.g.unwrap();
        let h = result.h.unwrap();

        // Build children recursively
        let child_a = self.build_from_subfunction(&g, first);
        let child_b = self.build_from_subfunction(&h, &rest_vars);

        // CRITICAL: Flatten children that use the same operator
        // This is what ensures canonicity for commutative operators
        let mut all_children = Vec::new();
        self.collect_flattened_children(&child_a, op, &mut all_children);
        self.collect_flattened_children(&child_b, op, &mut all_children);

        // Sort children by canonical hash for uniqueness
        all_children.sort_by_key(|c| c.canonical_hash());

        // Create n-ary interaction function
        let interaction = match op {
            Operator::And => InteractionFunction::and_all(all_children.len() as u32),
            Operator::Or => InteractionFunction::or_all(all_children.len() as u32),
            Operator::Xor => InteractionFunction::xor_all(all_children.len() as u32),
        };

        self.unique_table.internal(interaction, all_children)
    }

    /// Collect children, flattening nodes that use the same operator.
    ///
    /// If `node` is an internal node with the same operator, we recursively
    /// collect its children. Otherwise, we add the node itself.
    fn collect_flattened_children(&self, node: &Arc<CigNode>, op: Operator, children: &mut Vec<Arc<CigNode>>) {
        if let CigNodeKind::Internal {
            interaction,
            children: node_children,
        } = &node.kind
        {
            // Check if this node uses the same operator
            if let Some(node_op) = self.get_commutative_operator(interaction) {
                if node_op == op {
                    // Same operator: flatten by collecting this node's children
                    for child in node_children {
                        self.collect_flattened_children(child, op, children);
                    }
                    return;
                }
            }
        }

        // Different operator or leaf: add as-is
        children.push(node.clone());
    }

    /// Get the commutative operator if the interaction is one of AND/OR/XOR.
    fn get_commutative_operator(&self, interaction: &InteractionFunction) -> Option<Operator> {
        // Check if it's a pure AND/OR/XOR (any arity)
        let arity = interaction.arity();

        // Check AND
        let and_func = InteractionFunction::and_all(arity);
        if interaction == &and_func {
            return Some(Operator::And);
        }

        // Check OR
        let or_func = InteractionFunction::or_all(arity);
        if interaction == &or_func {
            return Some(Operator::Or);
        }

        // Check XOR
        let xor_func = InteractionFunction::xor_all(arity);
        if interaction == &xor_func {
            return Some(Operator::Xor);
        }

        None
    }

    /// Build from a subfunction on a specific variable set.
    fn build_from_subfunction(&mut self, g: &TruthTable, vars: &VarSet) -> Arc<CigNode> {
        // g is already a function on |vars| variables
        // We need to map it back to the original variable indices

        // Handle trivial cases
        if g.is_zero() {
            return self.unique_table.zero();
        }
        if g.is_one() {
            return self.unique_table.one();
        }

        let var_list: Vec<Var> = vars.iter().collect();

        // Check if it's just a single variable
        if var_list.len() == 1 {
            let var = var_list[0];
            // g is on 1 variable: either identity or negation
            if g.eval(&[false]) != g.eval(&[true]) {
                if g.eval(&[true]) {
                    return self.unique_table.leaf(var);
                } else {
                    // Negation
                    let leaf = self.unique_table.leaf(var);
                    let neg = InteractionFunction::from_expr(1, |x| !x[0]);
                    return self.unique_table.internal(neg, vec![leaf]);
                }
            }
        }

        // Create a truth table that maps to original variable positions
        let n = var_list.iter().map(|v| v.index()).max().unwrap();
        let f_remapped = TruthTable::from_expr(n, |x| {
            // Extract values for our variables
            let sub_vals: Vec<bool> = var_list.iter().map(|v| x[v.position()]).collect();
            g.eval(&sub_vals)
        });

        self.build_recursive(&f_remapped)
    }

    /// Get statistics about the builder.
    pub fn stats(&self) -> crate::cig::UniqueTableStats {
        self.unique_table.stats()
    }
}

// ============================================================================
// Helper functions for separability testing
// ============================================================================

/// Helper to test separability for CIG construction.
fn test_separability_on_function(f: &TruthTable, a_vars: &VarSet, b_vars: &VarSet) -> SeparabilityResult {
    let a_list: Vec<Var> = a_vars.iter().collect();
    let b_list: Vec<Var> = b_vars.iter().collect();

    let a_size = 1usize << a_list.len();
    let b_size = 1usize << b_list.len();

    let n = f.num_vars() as usize;

    // Build characteristic matrix
    let mut matrix = vec![vec![false; b_size]; a_size];
    let mut assignment = vec![false; n];

    for i in 0..a_size {
        for j in 0..b_size {
            for (k, &var) in a_list.iter().enumerate() {
                assignment[var.position()] = (i >> k) & 1 == 1;
            }
            for (k, &var) in b_list.iter().enumerate() {
                assignment[var.position()] = (j >> k) & 1 == 1;
            }
            matrix[i][j] = f.eval(&assignment);
        }
    }

    // Try each operator
    for op in Operator::all() {
        if let Some((u, v)) = check_rank_1(&matrix, op) {
            let g = TruthTable::from_expr(a_list.len() as u32, |x| {
                let idx = x.iter().enumerate().fold(0, |acc, (i, &b)| acc | ((b as usize) << i));
                u.get(idx).copied().unwrap_or(false)
            });

            let h = TruthTable::from_expr(b_list.len() as u32, |x| {
                let idx = x.iter().enumerate().fold(0, |acc, (i, &b)| acc | ((b as usize) << i));
                v.get(idx).copied().unwrap_or(false)
            });

            return SeparabilityResult {
                is_separable: true,
                operator: Some(op),
                g: Some(g),
                h: Some(h),
            };
        }
    }

    SeparabilityResult {
        is_separable: false,
        operator: None,
        g: None,
        h: None,
    }
}

struct SeparabilityResult {
    is_separable: bool,
    operator: Option<Operator>,
    g: Option<TruthTable>,
    h: Option<TruthTable>,
}

fn check_rank_1(matrix: &[Vec<bool>], op: Operator) -> Option<(Vec<bool>, Vec<bool>)> {
    match op {
        Operator::And => check_and_rank_1(matrix),
        Operator::Or => check_or_rank_1(matrix),
        Operator::Xor => check_xor_rank_1(matrix),
    }
}

fn check_and_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();
    let cols = matrix[0].len();

    let mut u = vec![false; rows];
    let mut v = vec![false; cols];

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if val {
                u[i] = true;
                v[j] = true;
            }
        }
    }

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if u[i] && v[j] && !val {
                return None;
            }
        }
    }

    Some((u, v))
}

fn check_or_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();
    let cols = matrix[0].len();

    let mut u = vec![true; rows];
    let mut v = vec![true; cols];

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if !val {
                u[i] = false;
                v[j] = false;
            }
        }
    }

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if !u[i] && !v[j] && val {
                return None;
            }
        }
    }

    Some((u, v))
}

fn check_xor_rank_1(matrix: &[Vec<bool>]) -> Option<(Vec<bool>, Vec<bool>)> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Some((vec![], vec![]));
    }

    let rows = matrix.len();

    let mut u = vec![false; rows];
    let v: Vec<bool> = matrix[0].clone();

    for (i, row) in matrix.iter().enumerate() {
        u[i] = row[0] ^ v[0];
    }

    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if (u[i] ^ v[j]) != val {
                return None;
            }
        }
    }

    Some((u, v))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::truth_table::named;

    #[test]
    fn test_build_constant() {
        let mut builder = CigBuilder::new();

        let zero = TruthTable::zero(3);
        let cig_zero = builder.build(&zero);
        assert!(cig_zero.root().is_constant());
        assert_eq!(cig_zero.root().as_constant(), Some(false));

        let one = TruthTable::one(3);
        let cig_one = builder.build(&one);
        assert!(cig_one.root().is_constant());
        assert_eq!(cig_one.root().as_constant(), Some(true));
    }

    #[test]
    fn test_build_variable() {
        let mut builder = CigBuilder::new();

        let x1 = TruthTable::var(3, Var(1));
        let cig = builder.build(&x1);

        assert!(cig.root().is_leaf());
        assert_eq!(cig.root().as_leaf(), Some(Var(1)));
    }

    #[test]
    fn test_build_xor() {
        let mut builder = CigBuilder::new();

        // x₁ ⊕ x₂
        let f = TruthTable::from_expr(2, |x| x[0] ^ x[1]);
        let cig = builder.build(&f);

        // Should be separable
        assert!(cig.root().is_internal());
        assert_eq!(cig.root().num_children(), 2);

        println!("XOR CIG:\n{}", cig);
    }

    #[test]
    fn test_build_parity_3_is_flat() {
        let mut builder = CigBuilder::new();

        // x₁ ⊕ x₂ ⊕ x₃ - should be a FLAT 3-ary XOR
        let f = TruthTable::from_expr(3, |x| x[0] ^ x[1] ^ x[2]);
        let cig = builder.build(&f);

        println!("Parity-3 CIG:\n{}", cig);

        // MUST be a single internal node with 3 children (not nested binary)
        assert!(cig.root().is_internal());
        assert_eq!(cig.root().num_children(), 3, "Parity-3 must have 3 children (flat n-ary)");
        assert_eq!(cig.depth(), 1, "Parity-3 must have depth 1 (flat)");
    }

    #[test]
    fn test_build_parity_5_is_flat() {
        let mut builder = CigBuilder::new();

        // x₁ ⊕ x₂ ⊕ x₃ ⊕ x₄ ⊕ x₅ - should be a FLAT 5-ary XOR
        let f = TruthTable::from_expr(5, |x| x.iter().fold(false, |acc, &b| acc ^ b));
        let cig = builder.build(&f);

        println!("Parity-5 CIG:\n{}", cig);

        // MUST be a single internal node with 5 children (not nested binary)
        assert!(cig.root().is_internal());
        assert_eq!(cig.root().num_children(), 5, "Parity-5 must have 5 children (flat n-ary)");
        assert_eq!(cig.depth(), 1, "Parity-5 must have depth 1 (flat)");
    }

    #[test]
    fn test_build_majority() {
        let mut builder = CigBuilder::new();

        let f = named::majority3();
        let cig = builder.build(&f);

        // Majority is irreducible
        assert!(cig.root().is_internal());
        assert_eq!(cig.root().num_children(), 3);
        assert_eq!(cig.interaction_width(), 3);

        println!("MAJ₃ CIG:\n{}", cig);
    }

    #[test]
    fn test_build_composed() {
        let mut builder = CigBuilder::new();

        // (x₁ ⊕ x₂) ∧ (x₃ ⊕ x₄)
        let f = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] ^ x[3]));
        let cig = builder.build(&f);

        println!("Composed CIG:\n{}", cig);
        println!("Size: {}", cig.size());
        println!("Depth: {}", cig.depth());
        println!("Width: {}", cig.interaction_width());

        // Root should be AND with 2 children (the two XOR subtrees)
        assert_eq!(cig.root().num_children(), 2);
    }

    #[test]
    fn test_equivalence() {
        let mut builder = CigBuilder::new();

        // Two equivalent functions built differently
        let f1 = TruthTable::from_expr(2, |x| x[0] && x[1]);
        let f2 = TruthTable::from_expr(2, |x| !(!x[0] || !x[1])); // De Morgan

        let cig1 = builder.build(&f1);
        let cig2 = builder.build(&f2);

        assert!(cig1.equivalent(&cig2));
    }

    #[test]
    fn test_canonicity_xor_order_independence() {
        let mut builder = CigBuilder::new();

        // Build x1 ⊕ x2 ⊕ x3 in different "conceptual orders"
        // They should all produce the SAME canonical CIG

        let f1 = TruthTable::from_expr(3, |x| x[0] ^ x[1] ^ x[2]);
        let f2 = TruthTable::from_expr(3, |x| x[2] ^ x[0] ^ x[1]);
        let f3 = TruthTable::from_expr(3, |x| (x[0] ^ x[1]) ^ x[2]);
        let f4 = TruthTable::from_expr(3, |x| x[0] ^ (x[1] ^ x[2]));

        let cig1 = builder.build(&f1);
        let cig2 = builder.build(&f2);
        let cig3 = builder.build(&f3);
        let cig4 = builder.build(&f4);

        // All should be equivalent
        assert!(cig1.equivalent(&cig2), "f1 ≡ f2");
        assert!(cig1.equivalent(&cig3), "f1 ≡ f3");
        assert!(cig1.equivalent(&cig4), "f1 ≡ f4");

        // All should have the same structure (pointer equality from unique table)
        assert_eq!(cig1.canonical_hash(), cig2.canonical_hash());
        assert_eq!(cig1.canonical_hash(), cig3.canonical_hash());
        assert_eq!(cig1.canonical_hash(), cig4.canonical_hash());
    }
}
