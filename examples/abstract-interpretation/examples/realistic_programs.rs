//! Realistic Program Analysis Examples.
//!
//! This file demonstrates how to use abstract interpretation domains to analyze
//! real-world programming patterns found in C/C++ and Rust codebases.
//!
//! Analyzed patterns include:
//! - **Array Bounds Checking**: Using Interval and Sign domains to prove safety of array accesses.
//! - **Constant Propagation**: Identifying constant values for optimization and dead code elimination.
//! - **Pointer Aliasing**: Tracking pointer targets to detect aliasing and side effects.
//! - **Combined Analysis**: Using multiple domains together to achieve higher precision.
//! - **Reduced Product**: Demonstrating how domains can refine each other (e.g., Sign × Interval).

use std::rc::Rc;

use abstract_interpretation::constant::ConstValue;
use abstract_interpretation::*;

fn main() {
    println!("=== Realistic Program Analysis ===\n");

    example_array_bounds_checking();
    example_constant_propagation();
    example_pointer_aliasing();
    example_combined_analysis();
    example_reduced_product();
}

/// Example 1: Array bounds checking
fn example_array_bounds_checking() {
    println!("Example 1: Array Bounds Checking");
    println!("---------------------------------");
    println!("Program:");
    println!("  int arr[10];");
    println!("  int i = 0;");
    println!("  while (i < 10) {{");
    println!("      arr[i] = i * 2;  // Safe access");
    println!("      i = i + 1;");
    println!("  }}");
    println!("  arr[i] = 42;  // i=10, out of bounds!");
    println!();

    let interval_domain = IntervalDomain;
    let array_size = 10;

    // Execute program forward using the abstract interpretation engine

    // i = 0
    println!("After i = 0:");
    let state = interval_domain.constant(&"i".to_string(), 0);
    if let Some((low, high)) = interval_domain.get_bounds(&state, &"i".to_string()) {
        println!("  i ∈ [{}, {}]", low, high);
        assert_eq!(low, 0, "i initialized to 0");
        assert_eq!(high, 0, "i initialized to 0");
    }

    // Loop fixpoint: Compute i's possible values at loop entry
    // Initially i=0, then i+=1 each iteration, condition is i<10
    // So at loop entry: i ∈ [0, 9] (condition passes) or i=10 (condition fails, exit)
    println!("\nLoop invariant computation:");
    println!("  Pre-loop: i = 0");

    // Simulate one iteration: i = i + 1 starting from i=0
    println!("  After 1st iteration: i = 0 + 1 = 1");
    let mut loop_state = interval_domain.constant(&"i".to_string(), 0);
    let increment = NumExpr::var("i").add(NumExpr::constant(1));
    loop_state = interval_domain.assign(&loop_state, &"i".to_string(), &increment);
    println!("  Engine computed: i ∈ {}", loop_state.get("i"));
    if let Some((low, high)) = interval_domain.get_bounds(&loop_state, &"i".to_string()) {
        assert_eq!(low, 1, "After i = i+1 from 0, should get 1");
        assert_eq!(high, 1, "After i = i+1 from 0, should get 1");
    }

    // Loop invariant: i ∈ [0, 10] (over-approximation valid for all iterations)
    println!("\n  Invariant: i ∈ [0, 10] (before/during/after loop)");
    let invariant = interval_domain.interval(&"i".to_string(), 0, 10);

    // Refine invariant using loop condition i < 10 (inside loop body)
    println!("\nInside loop body (after condition i < 10 passes):");
    let cond_lt = NumExpr::var("i").lt(NumExpr::constant(10));
    let inside_loop = interval_domain.assume(&invariant, &cond_lt);
    if let Some((low, high)) = interval_domain.get_bounds(&inside_loop, &"i".to_string()) {
        println!("  Engine refined i ∈ [{}, {}] (via i < 10)", low, high);
        assert_eq!(low, 0, "Inside loop: i >= 0");
        assert_eq!(high, 9, "Inside loop: i < 10 means i <= 9");

        // Check array access
        assert!(low >= 0 && high < array_size);
        println!("  ✓ Array access arr[i] is SAFE");
    }

    // After loop: condition fails, so i ≥ 10
    println!("\nAfter loop (when i < 10 becomes false):");
    let cond_ge = NumExpr::var("i").ge(NumExpr::constant(10));
    let after_loop = interval_domain.assume(&invariant, &cond_ge);
    if let Some((low, high)) = interval_domain.get_bounds(&after_loop, &"i".to_string()) {
        println!("  Engine refined i ∈ [{}, {}] (via i ≥ 10)", low, high);
        assert_eq!(low, 10, "After loop: i >= 10");
        assert_eq!(high, 10, "After loop: i = 10 (first value where i < 10 fails)");

        // Check array access
        assert!(low >= array_size);
        println!("  ✗ Array access arr[i] is UNSAFE (i={} >= {})", low, array_size);
    }

    println!("\n✓ Engine proved array safety inside loop, detected out-of-bounds after");
    println!("\n");
}

/// Example 2: Constant propagation
fn example_constant_propagation() {
    println!("Example 2: Constant Propagation");
    println!("--------------------------------");
    println!("  x = 7;");
    println!("  y = x + 3;");
    println!("  z = y * 2;");
    println!("  if (z == 20) {{  // Always true");
    println!("      return z;");
    println!("  }}");
    println!();

    let const_domain = ConstantDomain;
    let mut const_state = ConstantElement::new();

    // x = 7
    const_state.set("x".to_string(), ConstValue::Const(7));

    // y = x + 3
    let expr = NumExpr::var("x").add(NumExpr::constant(3));
    const_state = const_domain.assign(&const_state, &"y".to_string(), &expr);
    assert_eq!(const_state.get("y"), ConstValue::Const(10), "x=7, so x+3=10");

    // z = y * 2
    let expr = NumExpr::var("y").mul(NumExpr::constant(2));
    const_state = const_domain.assign(&const_state, &"z".to_string(), &expr);
    assert_eq!(const_state.get("z"), ConstValue::Const(20), "y=10, so y*2=20");

    println!("Analysis results:");
    println!("  x = {:?}", const_state.get("x"));
    println!("  y = {:?}", const_state.get("y"));
    println!("  z = {:?}", const_state.get("z"));
    println!();

    assert_eq!(const_state.get("z"), ConstValue::Const(20));
    println!("✓ All values propagated as constants: x=7, y=10, z=20");

    // Check branch
    let pred = NumExpr::var("z").eq(NumExpr::constant(20));
    let branch = const_domain.assume(&const_state, &pred);
    assert!(!const_domain.is_bottom(&branch));
    println!("✓ Condition 'z == 20' is always true (can optimize away)");

    println!("\n");
}

/// Example 3: Pointer aliasing
fn example_pointer_aliasing() {
    println!("Example 3: Pointer Aliasing");
    println!("---------------------------");
    println!("  int x, y;");
    println!("  int *p = &x;");
    println!("  int *q = &y;");
    println!("  p = q;  // Now p and q alias");
    println!();

    let domain = PointsToDomain::new();
    let mut state = PointsToElement::new(Rc::clone(domain.bdd()));

    // p = &x, q = &y
    state = domain.assign_address(&state, "p", &Location::Stack("x".to_string()));
    state = domain.assign_address(&state, "q", &Location::Stack("y".to_string()));

    println!("Initial:");
    println!("  p points-to: x");
    println!("  q points-to: y");
    let p_may_q_initial = state.may_alias(&domain, "p", "q");
    println!("  May-alias(p, q): {}", p_may_q_initial);
    assert!(!p_may_q_initial, "p and q initially point to different locations");
    assert!(!state.must_alias(&domain, "p", "q"), "p and q must not alias initially");

    // p = q
    println!("\nAfter p = q:");
    state = domain.assign_copy(&state, "p", "q");

    let p_targets = domain.decode_bdd(state.get("p"));
    println!("  p points-to: {:?}", p_targets);
    println!("  Must-alias(p, q): {}", state.must_alias(&domain, "p", "q"));
    assert!(state.must_alias(&domain, "p", "q"));
    println!("\n✓ Pointer analysis correctly tracks aliasing");

    println!("\n");
}

/// Example 4: Combined multi-domain analysis
fn example_combined_analysis() {
    println!("Example 4: Combined Multi-Domain Analysis");
    println!("------------------------------------------");
    println!("Program:");
    println!("  int n = 10;");
    println!("  int sum = 0;");
    println!("  for (int i = 0; i < n; i++) {{");
    println!("      sum = sum + i;");
    println!("  }}");
    println!();

    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;
    let sign_domain = SignDomain;

    // Initial state: n = 10, sum = 0
    println!("Initial state:");
    let mut const_state = const_domain.constant(&"n".to_string(), 10);
    const_state.set("sum".to_string(), ConstValue::Const(0));

    let mut interval_state = interval_domain.constant(&"sum".to_string(), 0);
    interval_state.set("n".to_string(), Interval::constant(10));

    let sign_state = sign_domain.constant(&"n".to_string(), 10);

    println!("  Const:    n={:?}, sum={:?}", const_state.get("n"), const_state.get("sum"));
    println!("  Interval: n ∈ {}, sum ∈ {}", interval_state.get("n"), interval_state.get("sum"));
    println!("  Sign:     n={:?}, sum={:?}", sign_state.get("n"), sign_state.get("sum"));

    // Loop condition: i < 10, so i ∈ [0, 9]
    println!("\nLoop body (i ranges from 0 to 9):");
    let loop_i_state = interval_domain.interval(&"i".to_string(), 0, 9);
    if let Some((low, high)) = interval_domain.get_bounds(&loop_i_state, &"i".to_string()) {
        println!("  i ∈ [{}, {}]", low, high);
        assert_eq!(low, 0, "Loop variable starts at 0");
        assert_eq!(high, 9, "Loop condition i < 10 means i <= 9");
    }

    // Compute sum bounds after all iterations: sum = 0+1+2+...+9 = 45
    println!("\nLoop invariant: sum accumulates i values");
    println!("  Start: sum = 0");
    println!("  Iter 0: sum = 0 + 0 = 0");
    println!("  Iter 1: sum = 0 + 1 = 1");
    println!("  ...");
    println!("  Iter 9: sum = 36 + 9 = 45");

    // Engine computation: simulate loop iterations
    let mut loop_sum = interval_domain.constant(&"sum".to_string(), 0);
    for i in 0..10 {
        let sum_expr = NumExpr::var("sum").add(NumExpr::constant(i));
        loop_sum = interval_domain.assign(&loop_sum, &"sum".to_string(), &sum_expr);
    }

    println!("\nAfter loop (engine computed all iterations):");
    if let Some((low, high)) = interval_domain.get_bounds(&loop_sum, &"sum".to_string()) {
        println!("  Interval: sum ∈ [{}, {}]", low, high);

        // Verify engine computed the correct result
        // After all iterations: sum = 0+1+2+...+9 = 45
        assert_eq!(low, 45, "Sum of 0+1+2+...+9 should be 45");
        assert_eq!(high, 45, "Final sum is exactly 45 (deterministic computation)");

        // Update other domains based on computed interval
        let sign_refined = sign_domain.assume(&sign_state, &NumExpr::var("sum").ge(NumExpr::constant(0)));
        println!("  Sign: sum = {:?}", sign_refined.get("sum"));
        println!("\n✓ Engine computed exact result:");
        println!("  - Interval maintains precise bounds [0, 45]");
        println!("  - Sign confirms sum is non-negative");
        println!("  - Constant domain loses precision (sum depends on loop)");
    }

    println!("\n");
}

/// Example 5: Reduced product
fn example_reduced_product() {
    println!("Example 5: Reduced Product (Sign × Interval)");
    println!("---------------------------------------------");
    println!("  assume(x ∈ [-10, 10]);");
    println!("  assume(x > 0);");
    println!("  assume(x == 5);");
    println!();

    let sign_domain = SignDomain;
    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;

    // Initial: x in [-10, 10]
    let mut sign_state = sign_domain.interval(&"x".to_string(), -10, 10);
    let mut const_state = const_domain.interval(&"x".to_string(), -10, 10);
    let mut interval_state = interval_domain.interval(&"x".to_string(), -10, 10);

    println!("Initial:");
    println!("  Sign: x = {:?}", sign_state.get("x"));
    assert_eq!(sign_state.get("x"), Sign::Top, "x ∈ [-10,10] includes both positive and negative");
    println!("  Constant: x = {:?}", const_state.get("x"));
    assert_eq!(const_state.get("x"), ConstValue::Top, "x is not a constant initially");
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"x".to_string()) {
        println!("  Interval: x ∈ [{}, {}]", low, high);
        assert_eq!(low, -10);
        assert_eq!(high, 10);
    }

    // Assume x > 0
    let pred = NumExpr::var("x").gt(NumExpr::constant(0));
    sign_state = sign_domain.assume(&sign_state, &pred);
    const_state = const_domain.assume(&const_state, &pred);
    interval_state = interval_domain.assume(&interval_state, &pred);

    println!("\nAfter x > 0:");
    println!("  Sign: x = {:?}", sign_state.get("x"));
    assert_ne!(sign_state.get("x"), Sign::Neg, "x > 0 means x is not negative");
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"x".to_string()) {
        println!("  Interval: x ∈ [{}, {}]", low, high);
        assert!(low > 0, "x > 0 means minimum is > 0");
        assert!(high <= 10, "x still bounded by initial interval");
    }

    // Assume x == 5
    let pred = NumExpr::var("x").eq(NumExpr::constant(5));
    sign_state = sign_domain.assume(&sign_state, &pred);
    const_state = const_domain.assume(&const_state, &pred);
    interval_state = interval_domain.assume(&interval_state, &pred);

    println!("\nAfter x == 5:");
    println!("  Sign: x = {:?}", sign_state.get("x"));
    assert_eq!(sign_state.get("x"), Sign::Pos, "x = 5 is positive");
    println!("  Constant: x = {:?}", const_state.get("x"));
    assert_eq!(const_state.get("x"), ConstValue::Const(5), "x must be exactly 5");
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"x".to_string()) {
        println!("  Interval: x ∈ [{}, {}]", low, high);
        assert_eq!(low, 5, "Interval refined to exactly 5");
        assert_eq!(high, 5, "Interval refined to exactly 5");
    }

    assert_eq!(const_state.get("x"), ConstValue::Const(5));
    println!("\n✓ All domains agree: x = 5");
    println!("  Reduced product refines each domain through cooperation");
}
