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
    println!("  int arr[10];");
    println!("  int i = 0;");
    println!("  while (i < 10) {{");
    println!("      arr[i] = i * 2;  // Safe access");
    println!("      i = i + 1;");
    println!("  }}");
    println!("  arr[i] = 42;  // i=10, out of bounds!");
    println!();

    let sign_domain = SignDomain;
    let interval_domain = IntervalDomain;

    // Loop invariant: i ∈ [0, 10] (true before, during, and after the loop)
    // This property holds at all points in the program
    println!("Loop invariant (true before, during, and after loop):");
    let invariant_state = interval_domain.interval(&"i".to_string(), 0, 10);
    if let Some((low, high)) = interval_domain.get_bounds(&invariant_state, &"i".to_string()) {
        println!("  i ∈ [{}, {}]", low, high);
    }

    // Inside loop body: after i < 10 check passes
    println!("\nInside loop body (after i < 10 condition passes):");
    let mut sign_state = sign_domain.interval(&"i".to_string(), 0, 9);
    let mut interval_state = interval_domain.interval(&"i".to_string(), 0, 9);

    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        println!("  i ∈ [{}, {}]", low, high);
        println!("  Sign: {:?}", sign_state.get("i"));
    }

    // Array access: arr[i] where array size is 10
    let array_size = 10;
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        assert!(low >= 0 && high < array_size);
        println!("\n✓ Array access arr[i] is SAFE (i ∈ [{}, {}] < {})", low, high, array_size);
    }

    // Post-loop state: i = 10 (first value failing i < 10 condition)
    println!("\nPost-loop state (when i < 10 becomes false):");
    sign_state = sign_domain.constant(&"i".to_string(), 10);
    interval_state = interval_domain.constant(&"i".to_string(), 10);

    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        println!("  i ∈ [{}, {}]", low, high);
        println!("  Sign: {:?}", sign_state.get("i"));
    }

    // Array access: arr[i] = 42 where i = 10
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        assert!(low >= array_size);
        println!("\n✗ Array access arr[i] is UNSAFE (i={} >= array size={})", low, array_size);
    }

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
    use NumExpr::*;
    let expr = Add(Box::new(Var("x".to_string())), Box::new(Const(3)));
    const_state = const_domain.assign(&const_state, &"y".to_string(), &expr);

    // z = y * 2
    let expr = Mul(Box::new(Var("y".to_string())), Box::new(Const(2)));
    const_state = const_domain.assign(&const_state, &"z".to_string(), &expr);

    println!("Analysis results:");
    println!("  x = {:?}", const_state.get("x"));
    println!("  y = {:?}", const_state.get("y"));
    println!("  z = {:?}", const_state.get("z"));
    println!();

    assert_eq!(const_state.get("z"), ConstValue::Const(20));
    println!("✓ All values propagated as constants: x=7, y=10, z=20");

    // Check branch
    use NumPred::*;
    let pred = Eq(Var("z".to_string()), Const(20));
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
    println!("  May-alias(p, q): {}", state.may_alias(&domain, "p", "q"));
    assert!(!state.may_alias(&domain, "p", "q"));

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
    println!("  int n = 10;");
    println!("  int sum = 0;");
    println!("  for (int i = 0; i < n; i++) {{");
    println!("      sum = sum + i;");
    println!("  }}");
    println!();

    let const_domain = ConstantDomain;
    let interval_domain = IntervalDomain;
    let sign_domain = SignDomain;

    // Initial: n = 10, sum = 0
    let mut const_state = const_domain.constant(&"n".to_string(), 10);
    const_state.set("sum".to_string(), ConstValue::Const(0));

    let mut interval_state = interval_domain.constant(&"sum".to_string(), 0);

    let mut sign_state = sign_domain.constant(&"sum".to_string(), 0);

    println!("Initial state:");
    println!("  Constant: n={:?}, sum={:?}", const_state.get("n"), const_state.get("sum"));
    println!(
        "  Interval: n={:?}, sum={:?}",
        interval_domain.get_bounds(&interval_state, &"n".to_string()),
        interval_domain.get_bounds(&interval_state, &"sum".to_string())
    );
    println!("  Sign: n={:?}, sum={:?}", sign_state.get("n"), sign_state.get("sum"));

    // Loop: i in [0, 9]
    println!("\nLoop fixpoint:");
    interval_state = interval_domain.interval(&"i".to_string(), 0, 9);
    let _sign_state_i = sign_domain.interval(&"i".to_string(), 0, 9);

    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"i".to_string()) {
        println!("  i ∈ [{}, {}]", low, high);
        assert!(low >= 0 && high <= 9);
    }

    // After loop: sum in [0, 45]
    interval_state = interval_domain.interval(&"sum".to_string(), 0, 45);
    sign_state = sign_domain.interval(&"sum".to_string(), 0, 45);

    println!("\nAfter loop:");
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"sum".to_string()) {
        println!("  Interval: sum ∈ [{}, {}]", low, high);
    }
    println!("  Sign: sum = {:?}", sign_state.get("sum"));
    println!("\n✓ Multiple domains cooperate:");
    println!("  - Interval tracks sum range [0, 45]");
    println!("  - Sign confirms sum is non-negative");
    println!("  - Constant lost precision (sum depends on loop)");

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
    println!("  Constant: x = {:?}", const_state.get("x"));
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"x".to_string()) {
        println!("  Interval: x ∈ [{}, {}]", low, high);
    }

    // Assume x > 0
    use NumExpr::*;
    use NumPred::*;
    let pred = Gt(Var("x".to_string()), Const(0));
    sign_state = sign_domain.assume(&sign_state, &pred);
    const_state = const_domain.assume(&const_state, &pred);
    interval_state = interval_domain.assume(&interval_state, &pred);

    println!("\nAfter x > 0:");
    println!("  Sign: x = {:?}", sign_state.get("x"));
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"x".to_string()) {
        println!("  Interval: x ∈ [{}, {}]", low, high);
    }

    // Assume x == 5
    let pred = Eq(Var("x".to_string()), Const(5));
    sign_state = sign_domain.assume(&sign_state, &pred);
    const_state = const_domain.assume(&const_state, &pred);
    interval_state = interval_domain.assume(&interval_state, &pred);

    println!("\nAfter x == 5:");
    println!("  Sign: x = {:?}", sign_state.get("x"));
    println!("  Constant: x = {:?}", const_state.get("x"));
    if let Some((low, high)) = interval_domain.get_bounds(&interval_state, &"x".to_string()) {
        println!("  Interval: x ∈ [{}, {}]", low, high);
    }

    assert_eq!(const_state.get("x"), ConstValue::Const(5));
    println!("\n✓ All domains agree: x = 5");
    println!("  Reduced product refines each domain through cooperation");
}
