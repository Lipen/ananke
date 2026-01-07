//! Path-Sensitive Interval Analysis with SDD Control Domain.
//!
//! This example demonstrates how **Sentential Decision Diagrams (SDDs)** can be used
//! instead of BDDs for path-sensitive abstract interpretation.
//!
//! **Key Idea:**
//! Combine an SDD control domain with a numeric interval domain to maintain separate
//! invariants for different control paths, enabling precise path-sensitive analysis.
//!
//! **Comparison to BDDs:**
//! - BDDs: Optimal for many Boolean functions, but can be memory-intensive in some cases.
//! - SDDs: More flexible encoding with potentially better compression for structured
//!   formulas, useful when control logic has special structure.
//!
//! **Topics covered:**
//! - Product domain construction (control + numeric)
//! - Path-sensitive refinement of program state
//! - Quantitative analysis of control path space

use abstract_interpretation::{AbstractDomain, IntervalDomain, ProductDomain, ProductElement, SddControlDomain};

fn main() {
    env_logger::init();
    println!("=== SDD-based Path-Sensitive Analysis ===");
    println!();

    example_two_path_analysis();
    example_control_refinement();
    example_path_space_analysis();

    println!("=== Analysis Complete ===");
}

/// Example 1: Two-path branching analysis
fn example_two_path_analysis() {
    println!("Example 1: Two-Path Branching Analysis");
    println!("──────────────────────────────────────");

    let sdd_control = SddControlDomain::new(2);
    let interval = IntervalDomain;

    println!("Program:");
    println!("  if (condition) {{");
    println!("    // path_a: numeric analysis applies here");
    println!("  }} else {{");
    println!("    // path_b: different numeric analysis");
    println!("  }}");
    println!();

    // Both paths are initially possible
    let path_a = sdd_control.mk_var_true("condition");
    let path_b = sdd_control.mk_var_false("condition");

    let state_a = ProductElement {
        control: path_a.clone(),
        numeric: interval.top(),
    };

    let state_b = ProductElement {
        control: path_b.clone(),
        numeric: interval.top(),
    };

    // Join: Both control paths are possible
    let _product = ProductDomain::new(sdd_control.clone(), interval.clone());
    let state = _product.join(&state_a, &state_b);

    println!("Initial state (both paths reachable):");
    println!("  Control is_top? {}", sdd_control.is_top(&state.control));
    println!("  Numeric: {:?}", state.numeric);
    assert!(sdd_control.is_top(&state.control));
    println!("✓ Control domain correctly identifies both paths are possible\n");
}

/// Example 2: Control path refinement
fn example_control_refinement() {
    println!("Example 2: Control Path Refinement");
    println!("──────────────────────────────────");

    let sdd_control = SddControlDomain::new(2);
    let interval = IntervalDomain;
    let _product = ProductDomain::new(sdd_control.clone(), interval.clone());

    println!("Assuming a particular control path becomes true:");
    println!();

    // Start with both paths possible
    let both = ProductElement {
        control: sdd_control.top(),
        numeric: interval.top(),
    };

    println!("Before refinement:");
    println!("  Control is_top? {}", sdd_control.is_top(&both.control));
    assert!(sdd_control.is_top(&both.control));
    println!();

    // Refine: Assume path_a is true
    let path_a_true = sdd_control.mk_var_true("path_a");
    let refined = ProductElement {
        control: sdd_control.meet(&both.control, &path_a_true),
        numeric: both.numeric.clone(),
    };

    println!("After assuming 'path_a = true':");
    println!("  Control is_top? {}", sdd_control.is_top(&refined.control));
    assert!(!sdd_control.is_top(&refined.control));
    println!("✓ Control domain correctly refined to single path\n");
}

/// Example 3: Quantitative analysis of path space
fn example_path_space_analysis() {
    println!("Example 3: Path Space Analysis");
    println!("──────────────────────────────");

    let domain = SddControlDomain::new(3);

    println!("Program with branching decisions:");
    println!("  if (flag1) {{ /* path 1 */ }}");
    println!("  if (flag2) {{ /* path 2 */ }}");
    println!("  if (flag3) {{ /* path 3 */ }}");
    println!("  Total control paths: 2^3 = 8");
    println!();

    let flag1 = domain.mk_var_true("flag1");
    let flag2 = domain.mk_var_true("flag2");
    let flag3 = domain.mk_var_true("flag3");

    // All three conditions true: only 1 path
    let all_true = domain.meet(&flag1, &domain.meet(&flag2, &flag3));
    let count_all_true = domain.model_count(&all_true);
    println!("Paths where all flags are true: {}", count_all_true);
    assert_eq!(count_all_true.to_string(), "1");
    println!("✓ Exactly 1 path (all flags = true)\n");

    // At least one flag true
    let at_least_one = domain.join(&flag1, &domain.join(&flag2, &flag3));
    let count_at_least = domain.model_count(&at_least_one);
    println!("Paths where at least one flag is true: {}", count_at_least);
    assert_eq!(count_at_least.to_string(), "7");
    println!("✓ 7 paths (all except all-false)\n");

    // Unconstrained (top): all paths reachable
    let all_paths = domain.top();
    let count_all = domain.model_count(&all_paths);
    println!("All possible paths (unconstrained): {}", count_all);
    assert_eq!(count_all.to_string(), "8");
    println!("✓ 8 total paths (2^3)\n");
}
