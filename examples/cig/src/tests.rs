//! Integration tests for the CIG crate.

use crate::analysis::{CigAnalysis, ComplexityClass};
use crate::builder::CigBuilder;
use crate::truth_table::{named, TruthTable};
use crate::variable::Var;

#[test]
fn test_full_workflow() {
    let mut builder = CigBuilder::new();

    // Build CIG for various functions
    let functions = [
        ("zero", TruthTable::zero(3)),
        ("one", TruthTable::one(3)),
        ("x1", TruthTable::var(3, Var(1))),
        ("and", named::and_all(2)),
        ("or", named::or_all(2)),
        ("xor", named::xor_all(2)),
        ("and3", named::and_all(3)),
        ("or3", named::or_all(3)),
        ("xor3", named::xor_all(3)),
        ("maj3", named::majority3()),
        ("mux", named::mux()),
    ];

    for (name, f) in &functions {
        let cig = builder.build(f);
        let analysis = CigAnalysis::analyze(&cig);

        println!("Function: {}", name);
        println!("  Size: {}", analysis.size);
        println!("  Depth: {}", analysis.depth);
        println!("  Width: {}", analysis.interaction_width);
        println!("  Class: {}", analysis.complexity_class);
        println!("  Operators: {:?}", analysis.operators_used);
        println!("  {:?}", cig);
        for line in format!("{}", cig).lines() {
            println!("  {}", line);
        }
        println!();
    }
}

#[test]
fn test_canonicity() {
    let mut builder = CigBuilder::new();

    // Different expressions for the same function
    let f1 = TruthTable::from_expr(3, |x| x[0] && (x[1] || x[2]));
    let f2 = TruthTable::from_expr(3, |x| (x[0] && x[1]) || (x[0] && x[2]));

    let cig1 = builder.build(&f1);
    let cig2 = builder.build(&f2);

    // They should be equivalent
    assert!(cig1.equivalent(&cig2), "Distributive law should produce equivalent CIGs");
}

#[test]
fn test_evaluation_consistency() {
    let mut builder = CigBuilder::new();

    // Test that CIG evaluation matches truth table
    let f = named::majority3();
    let cig = builder.build(&f);

    for i in 0..8 {
        let assignment = [i & 1 == 1, (i >> 1) & 1 == 1, (i >> 2) & 1 == 1];
        let tt_result = f.eval(&assignment);
        let cig_result = crate::operations::evaluate(&cig, &assignment);

        assert_eq!(tt_result, cig_result, "Evaluation mismatch at {:?}", assignment);
    }
}

#[test]
fn test_complexity_bounds() {
    let mut builder = CigBuilder::new();

    // Majority function should have high interaction width
    let maj = named::majority3();
    let cig = builder.build(&maj);
    let analysis = CigAnalysis::analyze(&cig);

    assert_eq!(analysis.interaction_width, 3, "MAJ3 should have width 3");
    assert!(analysis.bdd_width_lower_bound() >= 4, "BDD width bound for MAJ3");

    // XOR should be linear (regardless of interaction width)
    // N-ary XOR has width = arity, but is still a linear function
    let xor = named::xor_all(4);
    let cig = builder.build(&xor);
    let analysis = CigAnalysis::analyze(&cig);

    assert_eq!(analysis.interaction_width, 4, "4-ary XOR should have width 4");
    assert_eq!(analysis.complexity_class, ComplexityClass::Linear, "XOR should be linear");
}
