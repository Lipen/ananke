//! Operations on CIGs: conditioning, quantification, etc.

use std::collections::HashMap;
use std::sync::Arc;

use crate::cig::{Cig, CigNode, CigNodeKind, UniqueTable};
use crate::interaction::InteractionFunction;
use crate::variable::Var;

/// Condition a CIG by assigning a variable to a value.
///
/// Returns the CIG representing f|_{x=b}.
pub fn condition(cig: &Cig, var: Var, value: bool, table: &mut UniqueTable) -> Cig {
    let mut cache = HashMap::new();
    let new_root = condition_recursive(cig.root(), var, value, table, &mut cache);
    Cig::new(new_root)
}

fn condition_recursive(
    node: &Arc<CigNode>,
    var: Var,
    value: bool,
    table: &mut UniqueTable,
    cache: &mut HashMap<u64, Arc<CigNode>>,
) -> Arc<CigNode> {
    // Check cache
    if let Some(cached) = cache.get(&node.canonical_hash()) {
        return cached.clone();
    }

    let result = match &node.kind {
        CigNodeKind::Constant(_) => node.clone(),

        CigNodeKind::Leaf(v) => {
            if *v == var {
                if value {
                    table.one()
                } else {
                    table.zero()
                }
            } else {
                node.clone()
            }
        }

        CigNodeKind::Internal { interaction, children } => {
            // Recursively condition children
            let new_children: Vec<Arc<CigNode>> = children.iter().map(|c| condition_recursive(c, var, value, table, cache)).collect();

            // Simplify if any children became constants
            simplify_internal(interaction, new_children, table)
        }
    };

    cache.insert(node.canonical_hash(), result.clone());
    result
}

/// Simplify an internal node if children are constants.
fn simplify_internal(interaction: &InteractionFunction, children: Vec<Arc<CigNode>>, table: &mut UniqueTable) -> Arc<CigNode> {
    // Check if all children are constants
    let const_values: Option<Vec<bool>> = children.iter().map(|c| c.as_constant()).collect();

    if let Some(values) = const_values {
        // Evaluate the interaction function
        let result = interaction.eval(&values);
        return if result { table.one() } else { table.zero() };
    }

    // Check if any single constant simplifies things
    // For binary AND: if any child is 0, result is 0
    // For binary OR: if any child is 1, result is 1
    if children.len() == 2 {
        if let Some(op) = interaction.as_binary_operator() {
            use crate::Operator;
            match op {
                Operator::And => {
                    if children.iter().any(|c| c.as_constant() == Some(false)) {
                        return table.zero();
                    }
                    // Remove constant 1s
                    let non_const: Vec<_> = children.iter().filter(|c| c.as_constant() != Some(true)).cloned().collect();
                    if non_const.len() == 1 {
                        return non_const[0].clone();
                    }
                }
                Operator::Or => {
                    if children.iter().any(|c| c.as_constant() == Some(true)) {
                        return table.one();
                    }
                    // Remove constant 0s
                    let non_const: Vec<_> = children.iter().filter(|c| c.as_constant() != Some(false)).cloned().collect();
                    if non_const.len() == 1 {
                        return non_const[0].clone();
                    }
                }
                Operator::Xor => {
                    // XOR with 0 is identity, XOR with 1 is negation
                    let mut result_children = Vec::new();
                    let mut negate = false;
                    for child in &children {
                        match child.as_constant() {
                            Some(false) => {} // XOR with 0: skip
                            Some(true) => negate = !negate,
                            None => result_children.push(child.clone()),
                        }
                    }
                    if result_children.is_empty() {
                        return if negate { table.one() } else { table.zero() };
                    }
                    if result_children.len() == 1 && !negate {
                        return result_children[0].clone();
                    }
                    if result_children.len() == 1 && negate {
                        let neg = InteractionFunction::from_expr(1, |x| !x[0]);
                        return table.internal(neg, result_children);
                    }
                }
            }
        }
    }

    // No simplification possible
    table.internal(interaction.clone(), children)
}

/// Evaluate a CIG at a given assignment.
pub fn evaluate(cig: &Cig, assignment: &[bool]) -> bool {
    evaluate_node(cig.root(), assignment)
}

fn evaluate_node(node: &CigNode, assignment: &[bool]) -> bool {
    match &node.kind {
        CigNodeKind::Constant(v) => *v,
        CigNodeKind::Leaf(var) => assignment[var.position()],
        CigNodeKind::Internal { interaction, children } => {
            let child_values: Vec<bool> = children.iter().map(|c| evaluate_node(c, assignment)).collect();
            interaction.eval(&child_values)
        }
    }
}

/// Existentially quantify a variable: ∃x.f = f|_{x=0} ∨ f|_{x=1}
pub fn exists(cig: &Cig, var: Var, table: &mut UniqueTable) -> Cig {
    let f0 = condition(cig, var, false, table);
    let f1 = condition(cig, var, true, table);

    // Compute OR of the two results
    apply_or(&f0, &f1, table)
}

/// Universally quantify a variable: ∀x.f = f|_{x=0} ∧ f|_{x=1}
pub fn forall(cig: &Cig, var: Var, table: &mut UniqueTable) -> Cig {
    let f0 = condition(cig, var, false, table);
    let f1 = condition(cig, var, true, table);

    // Compute AND of the two results
    apply_and(&f0, &f1, table)
}

/// Apply OR to two CIGs.
pub fn apply_or(a: &Cig, b: &Cig, table: &mut UniqueTable) -> Cig {
    // Simple implementation: create OR node
    let interaction = InteractionFunction::from_binary(crate::Operator::Or);
    let node = table.internal(interaction, vec![a.root().clone(), b.root().clone()]);
    Cig::new(node)
}

/// Apply AND to two CIGs.
pub fn apply_and(a: &Cig, b: &Cig, table: &mut UniqueTable) -> Cig {
    let interaction = InteractionFunction::from_binary(crate::Operator::And);
    let node = table.internal(interaction, vec![a.root().clone(), b.root().clone()]);
    Cig::new(node)
}

/// Apply XOR to two CIGs.
pub fn apply_xor(a: &Cig, b: &Cig, table: &mut UniqueTable) -> Cig {
    let interaction = InteractionFunction::from_binary(crate::Operator::Xor);
    let node = table.internal(interaction, vec![a.root().clone(), b.root().clone()]);
    Cig::new(node)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::CigBuilder;
    use crate::truth_table::TruthTable;

    #[test]
    fn test_evaluate() {
        let mut builder = CigBuilder::new();

        // f = x₁ ∧ x₂
        let f = TruthTable::from_expr(2, |x| x[0] && x[1]);
        let cig = builder.build(&f);

        assert!(!evaluate(&cig, &[false, false]));
        assert!(!evaluate(&cig, &[true, false]));
        assert!(!evaluate(&cig, &[false, true]));
        assert!(evaluate(&cig, &[true, true]));
    }

    #[test]
    fn test_condition() {
        let mut builder = CigBuilder::new();
        let mut table = UniqueTable::new();

        // f = x₁ ∧ x₂
        let f = TruthTable::from_expr(2, |x| x[0] && x[1]);
        let cig = builder.build(&f);

        // f|_{x₁=0} = 0
        let cig_0 = condition(&cig, Var(1), false, &mut table);
        assert!(cig_0.root().as_constant() == Some(false));

        // f|_{x₁=1} = x₂
        let cig_1 = condition(&cig, Var(1), true, &mut table);
        assert!(cig_1.root().is_leaf() || cig_1.root().is_internal());
    }

    #[test]
    fn test_exists() {
        let mut builder = CigBuilder::new();
        let mut table = UniqueTable::new();

        // f = x₁ ∧ x₂
        // ∃x₁.f = (0 ∧ x₂) ∨ (1 ∧ x₂) = x₂
        let f = TruthTable::from_expr(2, |x| x[0] && x[1]);
        let cig = builder.build(&f);

        let cig_exists = exists(&cig, Var(1), &mut table);

        // Should evaluate to x₂
        assert!(!evaluate(&cig_exists, &[false, false]));
        assert!(!evaluate(&cig_exists, &[true, false]));
        assert!(evaluate(&cig_exists, &[false, true]));
        assert!(evaluate(&cig_exists, &[true, true]));
    }
}
