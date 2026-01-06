//! Constant Propagation Analysis Example.
//!
//! This example demonstrates **Constant Propagation**, a classic compiler optimization
//! technique implemented using abstract interpretation.
//!
//! The **Constant Domain** tracks whether a variable has a known constant value
//! at a specific program point.
//!
//! Applications demonstrated:
//! - **Constant Folding**: Evaluating expressions with constant operands at compile time.
//! - **Dead Code Elimination**: Identifying unreachable branches (e.g., `if (false) ...`).
//! - **Conditional Simplification**: Removing checks that are always true or always false.
//! - **Strength Reduction**: Replacing expensive operations with cheaper ones (e.g., `x * 2` → `x << 1`).

use abstract_interpretation::constant::{ConstValue, ConstantDomain, ConstantElement};
use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::expr::NumExpr;
use abstract_interpretation::numeric::NumericDomain;

fn main() {
    println!("=== Constant Propagation Analysis Examples ===\n");

    example_constant_folding();
    example_dead_code_elimination();
    example_conditional_simplification();
    example_optimization_opportunities();
}

/// Example 1: Constant folding
fn example_constant_folding() {
    println!("Example 1: Constant Folding");
    println!("----------------------------");

    let domain = ConstantDomain;

    println!("Program:");
    println!("  x = 5;");
    println!("  y = 3;");
    println!("  z = x + y;     // Can be folded to 8");
    println!("  w = z * 2;     // Can be folded to 16");
    println!("  result = w - 4; // Can be folded to 12");
    println!();

    let mut elem = ConstantElement::new();
    elem.set("x", ConstValue::Const(5));
    elem.set("y", ConstValue::Const(3));

    println!("Initial: x = {}, y = {}", elem.get("x"), elem.get("y"));

    // z = x + y
    let expr = NumExpr::Add(Box::new(NumExpr::Var("x".to_string())), Box::new(NumExpr::Var("y".to_string())));
    elem = domain.assign(&elem, "z", &expr);
    println!("After z = x + y: z = {}", elem.get("z"));

    // w = z * 2
    let expr = NumExpr::Mul(Box::new(NumExpr::Var("z".to_string())), Box::new(NumExpr::Const(2)));
    elem = domain.assign(&elem, "w", &expr);
    println!("After w = z * 2: w = {}", elem.get("w"));

    // result = w - 4
    let expr = NumExpr::Sub(Box::new(NumExpr::Var("w".to_string())), Box::new(NumExpr::Const(4)));
    elem = domain.assign(&elem, "result", &expr);
    println!("After result = w - 4: result = {}", elem.get("result"));

    println!("\n✓ Constant propagation eliminated all intermediate variables!");
    println!("  Optimized: result = 12");

    // Assertions
    assert_eq!(elem.get("z"), ConstValue::Const(8));
    assert_eq!(elem.get("w"), ConstValue::Const(16));
    assert_eq!(elem.get("result"), ConstValue::Const(12));

    println!("\n");
}

/// Example 2: Dead code elimination
fn example_dead_code_elimination() {
    println!("Example 2: Dead Code Elimination");
    println!("----------------------------------");

    let domain = ConstantDomain;

    println!("Program:");
    println!("  x = 5;");
    println!("  if (x > 10) {{  // Always false!");
    println!("    expensive_operation();");
    println!("  }}");
    println!("  if (x == 5) {{  // Always true!");
    println!("    guaranteed_operation();");
    println!("  }}");
    println!();

    let mut elem = ConstantElement::new();
    elem.set("x", ConstValue::Const(5));

    println!("State: x = {}", elem.get("x"));

    // Check: x > 10
    let pred = NumExpr::var("x").gt(NumExpr::constant(10));
    let branch1 = domain.assume(&elem, &pred);

    if domain.is_bottom(&branch1) {
        println!("✓ Branch 'x > 10' is DEAD CODE (always false)");
    }
    assert!(domain.is_bottom(&branch1));

    // Check: x == 5
    let pred = NumExpr::var("x").eq(NumExpr::constant(5));
    let branch2 = domain.assume(&elem, &pred);

    if !domain.is_bottom(&branch2) && branch2.get("x") == ConstValue::Const(5) {
        println!("✓ Branch 'x == 5' is ALWAYS TAKEN");
    }
    assert!(!domain.is_bottom(&branch2));

    println!("\n");
}

/// Example 3: Conditional simplification
fn example_conditional_simplification() {
    println!("Example 3: Conditional Simplification");
    println!("--------------------------------------");

    let domain = ConstantDomain;

    println!("Program:");
    println!("  DEBUG = 1;");
    println!("  if (DEBUG) {{");
    println!("    log('Debug info');");
    println!("  }}");
    println!();

    let mut elem = ConstantElement::new();
    elem.set("DEBUG", ConstValue::Const(1));

    println!("State: DEBUG = {}", elem.get("DEBUG"));

    // Check: DEBUG != 0
    let pred = NumExpr::var("DEBUG").neq(NumExpr::constant(0));
    let branch = domain.assume(&elem, &pred);

    if !domain.is_bottom(&branch) {
        println!("✓ DEBUG is always truthy, condition can be removed");
        println!("  Optimized: {{ log('Debug info'); }}");
    }
    assert!(!domain.is_bottom(&branch));

    println!();

    // Production build
    println!("Production build:");
    println!("  DEBUG = 0;");
    println!();

    elem.set("DEBUG", ConstValue::Const(0));
    println!("State: DEBUG = {}", elem.get("DEBUG"));

    let pred = NumExpr::var("DEBUG").neq(NumExpr::constant(0));
    let branch = domain.assume(&elem, &pred);

    if domain.is_bottom(&branch) {
        println!("✓ DEBUG is always false, entire block is dead code");
        println!("  Optimized: (removed)");
    }
    assert!(domain.is_bottom(&branch));

    println!("\n");
}

/// Example 4: Optimization opportunities
fn example_optimization_opportunities() {
    println!("Example 4: Optimization Opportunities");
    println!("--------------------------------------");

    let domain = ConstantDomain;

    println!("Program:");
    println!("  THRESHOLD = 100;");
    println!("  FACTOR = 2;");
    println!("  x = input();");
    println!("  if (x < THRESHOLD) {{");
    println!("    y = x * FACTOR;");
    println!("  }}");
    println!();

    let mut elem = ConstantElement::new();
    elem.set("THRESHOLD", ConstValue::Const(100));
    elem.set("FACTOR", ConstValue::Const(2));
    elem.set("x", ConstValue::Top); // Unknown input

    println!("Constants:");
    println!("  THRESHOLD = {}", elem.get("THRESHOLD"));
    println!("  FACTOR = {}", elem.get("FACTOR"));
    println!("  x = {}", elem.get("x"));
    println!();

    // Assume x < THRESHOLD (which is x < 100)
    let pred = NumExpr::var("x").lt(NumExpr::var("THRESHOLD"));
    elem = domain.assume(&elem, &pred);

    println!("After condition 'x < THRESHOLD':");
    println!("  x = {} (still unknown, but known < 100)", elem.get("x"));

    // y = x * FACTOR
    let expr = NumExpr::Mul(
        Box::new(NumExpr::Var("x".to_string())),
        Box::new(NumExpr::Var("FACTOR".to_string())),
    );
    elem = domain.assign(&elem, "y", &expr);

    println!("  y = x * FACTOR = {}", elem.get("y"));
    println!();

    println!("✓ Optimization: FACTOR is constant (2)");
    println!("  Optimized: y = x * 2  (can use shift: y = x << 1)");
    println!();

    // Another example with all constants
    println!("With constant input:");
    println!("  x = 42;");
    println!();

    let mut elem2 = ConstantElement::new();
    elem2.set("THRESHOLD", ConstValue::Const(100));
    elem2.set("FACTOR", ConstValue::Const(2));
    elem2.set("x", ConstValue::Const(42));

    let expr = NumExpr::Mul(
        Box::new(NumExpr::Var("x".to_string())),
        Box::new(NumExpr::Var("FACTOR".to_string())),
    );
    elem2 = domain.assign(&elem2, "y", &expr);

    println!("  y = x * FACTOR = {}", elem2.get("y"));
    println!("\n✓ Complete constant propagation: y = 84");

    // Assertions
    assert_eq!(elem2.get("y"), ConstValue::Const(84));

    println!("\n");
}
