//! SDD Control Domain Analysis Example.
//!
//! This example demonstrates the **SDD Control Domain** for path-sensitive abstract interpretation.
//! SDDs (Sentential Decision Diagrams) are an alternative to BDDs for Boolean function representation
//! with potentially better compression for structured formulas.
//!
//! **Topics covered:**
//! - Boolean constraint satisfaction and logical operations
//! - Implication checking and logical reasoning
//! - Model counting (quantitative reasoning about constraint satisfaction)

use abstract_interpretation::{AbstractDomain, SddControlDomain};

fn main() {
    env_logger::init();
    println!("=== SDD Control Domain Analysis ===");
    println!();

    example_boolean_constraints();
    example_implication_checking();
    example_model_counting();

    println!("=== Analysis Complete ===");
}

/// Example 1: Boolean constraints with SDDs
fn example_boolean_constraints() {
    println!("Example 1: Boolean Constraints with SDDs");
    println!("────────────────────────────────────────");

    let domain = SddControlDomain::new(2);

    println!("Program description:");
    println!("  Tracking control paths with two boolean flags: mode, error");
    println!();

    // Create control states
    let mode_on = domain.mk_var_true("mode");
    let mode_off = domain.mk_var_false("mode");
    let error = domain.mk_var_true("error");

    println!("Initial states:");
    println!("  mode = true  {:?}", mode_on);
    println!("  mode = false {:?}", mode_off);
    println!("  error = true {:?}", error);
    println!();

    // Join to get all mode possibilities
    let any_mode = domain.join(&mode_on, &mode_off);
    println!("After joining both modes: is_top = {}", domain.is_top(&any_mode));
    assert!(domain.is_top(&any_mode));
    println!("✓ Correctly identifies that mode has no constraint\n");

    // Path where mode is on and no error
    let ok_path = domain.meet(&mode_on, &domain.not(&error));
    println!("Paths where (mode AND NOT error):");
    println!("  Model count: {}", domain.model_count(&ok_path));
    assert_eq!(domain.model_count(&ok_path).to_string(), "1");
    println!("✓ Exactly one satisfying assignment (as expected)\n");

    // Impossible path: mode on and mode off together
    let impossible = domain.meet(&mode_on, &mode_off);
    println!("Attempting to satisfy (mode AND NOT mode):");
    println!("  is_bottom? {}", domain.is_bottom(&impossible));
    assert!(domain.is_bottom(&impossible));
    println!("✓ Correctly identifies contradiction\n");
}

/// Example 2: Implication and reasoning
fn example_implication_checking() {
    println!("Example 2: Implication Checking");
    println!("───────────────────────────────");

    let domain = SddControlDomain::new(3);

    println!("Demonstrating logical implications:");
    println!();

    let x = domain.mk_var_true("x");
    let y = domain.mk_var_true("y");
    let x_and_y = domain.and(&x, &y);
    let x_or_y = domain.or(&x, &y);

    // x ∧ y ⇒ x ∨ y should always hold
    let implies = domain.implies(&x_and_y, &x_or_y);
    println!("(x AND y) implies (x OR y)? {}", implies);
    assert!(implies);
    println!("✓ Logical implication verified\n");

    // x ∧ y should NOT imply NOT x
    let not_x = domain.not(&x);
    let implies_not = domain.implies(&x_and_y, &not_x);
    println!("(x AND y) implies NOT x? {}", implies_not);
    assert!(!implies_not);
    println!("✓ Correctly rejects invalid implication\n");
}

/// Example 3: Model counting (quantitative analysis)
fn example_model_counting() {
    println!("Example 3: Model Counting");
    println!("─────────────────────────");

    let domain = SddControlDomain::new(3);

    println!("Counting satisfying assignments for boolean formulas:");
    println!();

    let a = domain.mk_var_true("a");
    let b = domain.mk_var_true("b");

    // a ∧ b: only one assignment (a=T, b=T, c can be anything)
    let and_ab = domain.meet(&a, &b);
    let count_and = domain.model_count(&and_ab);
    println!("Models satisfying (a AND b) with 3 variables: {}", count_and);
    // With 3 variables, c can be T or F, so 2 models
    assert_eq!(count_and.to_string(), "2");
    println!("✓ Correct: a=T, b=T, c∈{{T,F}} gives 2 assignments\n");

    // a ∨ b: multiple assignments
    let or_ab = domain.join(&a, &b);
    let count_or = domain.model_count(&or_ab);
    println!("Models satisfying (a OR b) with 3 variables: {}", count_or);
    // Count: (a ∨ b) = true in all but (a=F, b=F)
    // So 8 total - 2 (where c varies) = 6 models
    assert_eq!(count_or.to_string(), "6");
    println!("✓ Correct: all assignments except a=F,b=F (total 6)\n");

    // Top (tautology): all assignments satisfy
    let top = domain.top();
    let count_top = domain.model_count(&top);
    println!("Models satisfying ⊤ with 3 variables: {}", count_top);
    assert_eq!(count_top.to_string(), "8");
    println!("✓ Correct: 2^3 = 8 total assignments\n");
}
