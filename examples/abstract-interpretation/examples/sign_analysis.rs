//! Sign Analysis Example.
//!
//! This example demonstrates **Sign Analysis**, a classic abstract interpretation
//! domain that tracks the sign of variables: Positive, Negative, Zero, or combinations (Top).
//!
//! Applications demonstrated:
//! - **Division by Zero Detection**: Proving that a divisor is strictly non-zero (e.g., Positive).
//! - **Dead Code Elimination**: Proving that a condition like `x * x < 0` is impossible.
//! - **Loop Invariants**: Proving that a loop counter `i` remains non-negative.
//! - **Overflow Safety**: Reasoning about the sign of results even when exact values are unknown.

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::expr::NumExpr;
use abstract_interpretation::numeric::NumericDomain;
use abstract_interpretation::sign::{Sign, SignDomain, SignElement};

fn main() {
    println!("=== Sign Domain Analysis Examples ===\n");

    example_division_by_zero();
    example_conditional_analysis();
    example_loop_analysis();
    example_overflow_detection();
}

/// Example 1: Division by zero detection
fn example_division_by_zero() {
    println!("Example 1: Division by Zero Detection");
    println!("--------------------------------------");

    let domain = SignDomain;

    // Program: if (x > 0) { y = 100 / x; }
    println!("Program:");
    println!("  if (x > 0) {{");
    println!("    y = 100 / x;  // Safe: x is positive");
    println!("  }}");
    println!();

    let mut elem = SignElement::new();
    elem.set("x", Sign::Top); // x is unknown initially

    println!("Initial state: x = {}", elem.get("x"));

    // Assume x > 0
    let pred = NumExpr::var("x").gt(NumExpr::constant(0));
    let elem = domain.assume(&elem, &pred);

    println!("After 'x > 0': x = {}", elem.get("x"));

    // Check if division is safe
    if elem.get("x") == Sign::Pos {
        println!("✓ Division by x is SAFE (x is strictly positive)");
    } else if elem.get("x").has_zero() {
        println!("⚠ Division by x might be UNSAFE (x could be zero)");
    }
    assert_eq!(elem.get("x"), Sign::Pos);

    println!();

    // Unsafe case
    println!("Unsafe case:");
    println!("  if (x <= 0) {{");
    println!("    y = 100 / x;  // UNSAFE: x could be zero!");
    println!("  }}");
    println!();

    let mut elem = SignElement::new();
    elem.set("x", Sign::Top);

    let pred = NumExpr::var("x").le(NumExpr::constant(0));
    let elem = domain.assume(&elem, &pred);

    println!("After 'x <= 0': x = {}", elem.get("x"));

    if elem.get("x").has_zero() {
        println!("✗ Division by x is UNSAFE (x could be zero)");
    }
    assert!(elem.get("x").has_zero());

    println!("\n");
}

/// Example 2: Conditional branch analysis
fn example_conditional_analysis() {
    println!("Example 2: Conditional Branch Analysis");
    println!("---------------------------------------");

    let domain = SignDomain;

    println!("Program:");
    println!("  x = input();");
    println!("  if (x * x < 0) {{  // Always false!");
    println!("    unreachable_code();");
    println!("  }}");
    println!();

    let mut elem = SignElement::new();
    elem.set("x", Sign::Top); // x can be any value

    println!("Initial: x = {}", elem.get("x"));

    // Evaluate x * x
    let expr = NumExpr::var("x").mul(NumExpr::var("x"));

    let result = domain.assign(&elem, "temp", &expr);
    let sign_of_square = result.get("temp");

    println!("Sign of x*x: {}", sign_of_square);

    // Check if x*x < 0 is possible
    if sign_of_square == Sign::NonNeg {
        println!("✓ Dead code detected: x*x is always ≥ 0, condition 'x*x < 0' is always false");
    }
    assert_eq!(sign_of_square, Sign::NonNeg);

    println!("\n");
}

/// Example 3: Loop analysis with sign tracking
fn example_loop_analysis() {
    println!("Example 3: Loop Analysis");
    println!("------------------------");

    let domain = SignDomain;

    println!("Program:");
    println!("  i = 0;");
    println!("  while (i < 10) {{");
    println!("    process(i);");
    println!("    i = i + 1;");
    println!("  }}");
    println!();

    // Initial state
    let mut elem = domain.constant("i", 0);
    println!("Initial: i = {}", elem.get("i"));

    // First iteration: i = 0 + 1
    let expr = NumExpr::var("i").add(NumExpr::constant(1));
    elem = domain.assign(&elem, "i", &expr);
    println!("After i = i + 1: i = {}", elem.get("i"));

    // Second iteration: Pos + 1
    elem = domain.assign(&elem, "i", &expr);
    println!("After i = i + 1: i = {}", elem.get("i"));

    // Simulate fixpoint with join: Zero ⊔ Pos = NonNeg
    let initial = domain.constant("i", 0);
    elem = domain.join(&initial, &elem);
    println!("After join with initial (fixpoint): i = {}", elem.get("i"));

    // Fixpoint reached
    println!("\n✓ Fixpoint: i is {} (includes both 0 and positive values)", elem.get("i"));
    println!("  This guarantees i is always non-negative in the loop");

    assert_eq!(elem.get("i"), Sign::NonNeg);

    println!("\n");
}

/// Example 4: Overflow detection
fn example_overflow_detection() {
    println!("Example 4: Arithmetic Overflow Analysis");
    println!("---------------------------------------");

    let domain = SignDomain;

    println!("Program:");
    println!("  if (x > 0 && y > 0) {{");
    println!("    z = x + y;  // Could overflow, but maintains positivity");
    println!("  }}");
    println!();

    let mut elem = SignElement::new();
    elem.set("x", Sign::Top);
    elem.set("y", Sign::Top);

    // Assume x > 0
    let pred = NumExpr::var("x").gt(NumExpr::constant(0));
    elem = domain.assume(&elem, &pred);

    // Assume y > 0
    let pred = NumExpr::var("y").gt(NumExpr::constant(0));
    elem = domain.assume(&elem, &pred);

    println!("After 'x > 0 && y > 0':");
    println!("  x = {}", elem.get("x"));
    println!("  y = {}", elem.get("y"));

    // z = x + y
    let expr = NumExpr::var("x").add(NumExpr::var("y"));
    let result = domain.assign(&elem, "z", &expr);

    println!("  z = x + y: {}", result.get("z"));

    assert_eq!(result.get("z"), Sign::Pos); // Pos + Pos = Pos

    println!("\n✓ Sign analysis: z is strictly positive");
    println!("  (Note: Overflow is abstracted away; we track sign properties only)");
}
