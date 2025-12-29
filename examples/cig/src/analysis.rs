//! Structural analysis of CIGs.
//!
//! This module provides tools for analyzing the complexity and structure
//! of Boolean functions through their CIG representation.

use std::fmt;

use crate::cig::{Cig, CigNode, CigNodeKind};
use crate::interaction::Operator;
use crate::variable::Var;

/// Analysis results for a CIG.
#[derive(Debug, Clone)]
pub struct CigAnalysis {
    /// Number of nodes in the CIG.
    pub size: usize,
    /// Maximum depth of the CIG.
    pub depth: usize,
    /// Interaction width (max arity).
    pub interaction_width: usize,
    /// Total interaction table size.
    pub table_size: usize,
    /// Number of variables.
    pub num_variables: usize,
    /// Number of internal nodes.
    pub num_internal: usize,
    /// Number of leaf nodes.
    pub num_leaves: usize,
    /// Complexity classification.
    pub complexity_class: ComplexityClass,
    /// Operators used in the decomposition.
    pub operators_used: Vec<Operator>,
}

impl CigAnalysis {
    /// Analyze a CIG.
    pub fn analyze(cig: &Cig) -> Self {
        let vars = cig.variables();
        let mut num_internal = 0;
        let mut num_leaves = 0;
        let mut operators = Vec::new();

        count_nodes(cig.root(), &mut num_internal, &mut num_leaves, &mut operators);

        operators.sort_by_key(|op| *op as u8);
        operators.dedup();

        let width = cig.interaction_width();
        let complexity_class = classify(width, cig.depth(), &operators, vars.len());

        CigAnalysis {
            size: cig.size(),
            depth: cig.depth(),
            interaction_width: width,
            table_size: cig.table_size(),
            num_variables: vars.len(),
            num_internal,
            num_leaves,
            complexity_class,
            operators_used: operators,
        }
    }

    /// Get the BDD width lower bound.
    pub fn bdd_width_lower_bound(&self) -> usize {
        if self.interaction_width == 0 {
            1
        } else {
            1usize << (self.interaction_width - 1)
        }
    }
}

fn count_nodes(node: &CigNode, internal: &mut usize, leaves: &mut usize, operators: &mut Vec<Operator>) {
    match &node.kind {
        CigNodeKind::Constant(_) => {}
        CigNodeKind::Leaf(_) => *leaves += 1,
        CigNodeKind::Internal { interaction, children } => {
            *internal += 1;
            // Try to recognize symmetric operators (AND/OR/XOR) of any arity
            if let Some(op) = interaction.as_symmetric_operator() {
                operators.push(op);
            } else if let Some(op) = interaction.as_binary_operator() {
                // Fallback to binary operator check
                operators.push(op);
            }
            for child in children {
                count_nodes(child, internal, leaves, operators);
            }
        }
    }
}

/// Complexity classification based on interaction structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComplexityClass {
    /// Constant function (no variables).
    Constant,
    /// Single variable (projection).
    Projection,
    /// Linear function (all XOR).
    Linear,
    /// Monotone function (all AND/OR).
    Monotone,
    /// Mixed but separable (low width).
    Separable,
    /// Irreducible (high interaction).
    Irreducible,
}

impl ComplexityClass {
    /// Get a description of this complexity class.
    pub fn description(&self) -> &'static str {
        match self {
            ComplexityClass::Constant => "constant (no variables)",
            ComplexityClass::Projection => "single variable projection",
            ComplexityClass::Linear => "linear (XOR of variables)",
            ComplexityClass::Monotone => "monotone (AND/OR tree)",
            ComplexityClass::Separable => "separable (low interaction)",
            ComplexityClass::Irreducible => "irreducible (high interaction)",
        }
    }
}

impl fmt::Display for ComplexityClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.description())
    }
}

fn classify(width: usize, depth: usize, operators: &[Operator], num_vars: usize) -> ComplexityClass {
    // Constant function
    if num_vars == 0 {
        return ComplexityClass::Constant;
    }

    // Single variable functions
    if num_vars == 1 {
        assert!(depth <= 1, "Single variable CIG must have depth <= 1, got depth {}", depth);
        return ComplexityClass::Projection;
    }

    // Multi-variable functions
    // If operators is empty, it must use non-standard interaction (irreducible)
    if operators.is_empty() {
        return ComplexityClass::Irreducible;
    }

    // Classification order prioritizes operator type over width:
    // 1. Linear: XOR functions are linear regardless of arity (x1 ⊕ x2 ⊕ ... ⊕ xn)
    if operators.iter().all(|&op| op == Operator::Xor) {
        return ComplexityClass::Linear;
    }

    // 2. Monotone: AND/OR functions are monotone regardless of arity
    //    (e.g., x1 ∧ x2 ∧ x3 can be decomposed as (x1 ∧ x2) ∧ x3, always separable)
    if operators.iter().all(|&op| op == Operator::And || op == Operator::Or) {
        return ComplexityClass::Monotone;
    }

    // 3. Separable: width <= 2 (low interaction, mixed operators)
    if width <= 2 {
        return ComplexityClass::Separable;
    }

    // 4. Irreducible: width > 2 with non-pure operators (mixed AND/OR)
    //    (e.g., majority functions: width 3, non-separable structure)
    ComplexityClass::Irreducible
}

/// Suggested variable ordering based on CIG structure.
pub fn suggest_variable_order(cig: &Cig) -> Vec<Var> {
    let mut order = Vec::new();
    collect_var_order(cig.root(), &mut order);
    order
}

fn collect_var_order(node: &CigNode, order: &mut Vec<Var>) {
    match &node.kind {
        CigNodeKind::Constant(_) => {}
        CigNodeKind::Leaf(v) => {
            if !order.contains(v) {
                order.push(*v);
            }
        }
        CigNodeKind::Internal { children, .. } => {
            for child in children {
                collect_var_order(child, order);
            }
        }
    }
}

/// Generate a summary report for a CIG.
pub fn summary_report(cig: &Cig) -> String {
    let analysis = CigAnalysis::analyze(cig);

    let ops_str = if analysis.operators_used.is_empty() {
        "none".to_string()
    } else {
        analysis.operators_used.iter().map(|op| op.symbol()).collect::<Vec<_>>().join(", ")
    };

    format!(
        r#"CIG Analysis Report
═══════════════════════════════════════
Variables:        {}
Size:             {} nodes
Depth:            {}
Interaction width: {}
Table size:       {} entries

Structure:
  Internal nodes: {}
  Leaf nodes:     {}
  Operators:      {}

Complexity: {}

BDD width lower bound: ≥ {}
"#,
        analysis.num_variables,
        analysis.size,
        analysis.depth,
        analysis.interaction_width,
        analysis.table_size,
        analysis.num_internal,
        analysis.num_leaves,
        ops_str,
        analysis.complexity_class,
        analysis.bdd_width_lower_bound()
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::CigBuilder;
    use crate::truth_table::{named, TruthTable};

    #[test]
    fn test_analysis_constant() {
        let mut builder = CigBuilder::new();
        let f = TruthTable::zero(3);
        let cig = builder.build(&f);
        let analysis = CigAnalysis::analyze(&cig);

        assert_eq!(analysis.complexity_class, ComplexityClass::Constant);
    }

    #[test]
    fn test_analysis_linear() {
        let mut builder = CigBuilder::new();
        let f = named::xor_all(3);
        let cig = builder.build(&f);
        let analysis = CigAnalysis::analyze(&cig);

        assert_eq!(analysis.complexity_class, ComplexityClass::Linear);
    }

    #[test]
    fn test_analysis_irreducible() {
        let mut builder = CigBuilder::new();
        let f = named::majority3();
        let cig = builder.build(&f);
        let analysis = CigAnalysis::analyze(&cig);

        assert_eq!(analysis.complexity_class, ComplexityClass::Irreducible);
        assert_eq!(analysis.interaction_width, 3);
        assert!(analysis.bdd_width_lower_bound() >= 4);
    }

    #[test]
    fn test_summary_report() {
        let mut builder = CigBuilder::new();
        let f = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] || x[3]));
        let cig = builder.build(&f);
        let report = summary_report(&cig);

        println!("{}", report);
        assert!(report.contains("Variables:"));
        assert!(report.contains("Depth:"));
    }

    #[test]
    fn test_nary_and_is_monotone() {
        let mut builder = CigBuilder::new();
        // 3-ary AND: should be Monotone, not Irreducible
        let f = TruthTable::from_expr(3, |x| x[0] && x[1] && x[2]);
        let cig = builder.build(&f);
        let analysis = CigAnalysis::analyze(&cig);

        assert_eq!(analysis.interaction_width, 3, "3-ary AND should have width 3");
        assert_eq!(
            analysis.complexity_class,
            ComplexityClass::Monotone,
            "3-ary AND should be Monotone (AND-tree), not Irreducible"
        );
    }

    #[test]
    fn test_nary_or_is_monotone() {
        let mut builder = CigBuilder::new();
        // 4-ary OR: should be Monotone, not Irreducible
        let f = TruthTable::from_expr(4, |x| x[0] || x[1] || x[2] || x[3]);
        let cig = builder.build(&f);
        let analysis = CigAnalysis::analyze(&cig);

        assert_eq!(analysis.interaction_width, 4, "4-ary OR should have width 4");
        assert_eq!(
            analysis.complexity_class,
            ComplexityClass::Monotone,
            "4-ary OR should be Monotone (OR-tree), not Irreducible"
        );
    }

    #[test]
    fn test_majority_is_irreducible() {
        let mut builder = CigBuilder::new();
        // Majority is non-monotone with width 3: truly irreducible
        let f = named::majority3();
        let cig = builder.build(&f);
        let analysis = CigAnalysis::analyze(&cig);

        assert_eq!(analysis.interaction_width, 3, "MAJ3 should have width 3");
        assert_eq!(
            analysis.complexity_class,
            ComplexityClass::Irreducible,
            "Majority should be Irreducible (mixed operators, not pure AND/OR/XOR)"
        );
    }
}
