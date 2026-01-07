//! Dynamic Type Checking Example.
//!
//! This example demonstrates using the **Type Domain** to analyze a dynamically typed
//! program (simulated).
//!
//! Scenario:
//! A function receives an input `x` that can be an Integer or a String.
//! - If it's an Integer, it adds 1.
//! - If it's a String, it returns the length.
//!
//! The analysis proves that `y` (the result) is ALWAYS an Integer, regardless of the input type.

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::type_domain::{Type, TypeDomain};

fn main() {
    env_logger::init();
    println!("=== Dynamic Type Checking Analysis ===\n");

    println!("Demonstrating type inference for dynamic code.\n");

    let domain = TypeDomain;

    // 1. Initial State: x can be Integer OR String
    // x ∈ {Integer, String}
    let t_int = domain.from_type(Type::Integer);
    let t_str = domain.from_type(Type::String);
    let x_type = domain.join(&t_int, &t_str);

    println!("Initial State:");
    println!("  x type: {:?}", x_type);
    assert!(domain.may_be(&x_type, Type::Integer));
    assert!(domain.may_be(&x_type, Type::String));
    assert!(!domain.may_be(&x_type, Type::Boolean));

    // 2. Branching based on type check
    println!("\nProgram:");
    println!("  if (typeof(x) == Integer) {{");
    println!("    y = x + 1;");
    println!("  }} else {{");
    println!("    y = len(x);");
    println!("  }}");

    // Branch 1: typeof(x) == Integer
    // Refine x to Integer
    let x_branch1 = domain.meet(&x_type, &t_int);
    println!("\nBranch 1 (Integer path):");
    println!("  x type: {:?}", x_branch1);

    // y = x + 1 (Integer + Integer -> Integer)
    let y_branch1 = domain.from_type(Type::Integer);
    println!("  y type: {:?}", y_branch1);

    // Branch 2: typeof(x) != Integer (so it must be String in our universe)
    // Refine x to String
    let x_branch2 = domain.meet(&x_type, &t_str);
    println!("\nBranch 2 (String path):");
    println!("  x type: {:?}", x_branch2);

    // y = len(x) (Length returns Integer)
    let y_branch2 = domain.from_type(Type::Integer);
    println!("  y type: {:?}", y_branch2);

    // 3. Join branches
    let x_final = domain.join(&x_branch1, &x_branch2);
    let y_final = domain.join(&y_branch1, &y_branch2);
    println!("\nFinal Result:");
    println!("  x type: {:?}", x_final);
    println!("  y type: {:?}", y_final);

    // Verify property: y is always Integer
    if domain.is_exactly(&y_final, Type::Integer) {
        println!("  ✓ Verified: Result 'y' is always an Integer.");
    } else {
        println!("  ✗ Failed: Result 'y' might not be an Integer.");
    }
    assert!(domain.is_exactly(&y_final, Type::Integer), "Result 'y' should be exactly Integer");
}
