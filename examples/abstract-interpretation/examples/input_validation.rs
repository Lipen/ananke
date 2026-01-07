//! Input Validation Analysis Example.
//!
//! This example demonstrates how to use the **String Length Domain** to verify
//! input validation logic.
//!
//! Scenario:
//! A password validation routine checks if the input length is at least 8 characters.
//!
//! The analysis proves:
//! 1. In the "valid" branch, the password length is guaranteed to be ≥ 8.
//! 2. In the "invalid" branch, the password length is guaranteed to be < 8 (specifically [0, 7]).
//!
//! This ensures that the validation logic correctly partitions the input space.

use abstract_interpretation::*;

fn main() {
    env_logger::init();
    println!("=== Input Validation Analysis ===\n");

    println!("This example demonstrates analyzing input validation logic using string length abstraction.");
    println!("Scenario: Validating that a password meets minimum length requirements.");

    println!("\nProgram being analyzed:");
    println!("  password = input();");
    println!("  assume(len(password) >= 0); // Implicit");
    println!("  if (len(password) >= 8) {{");
    println!("    // Valid password");
    println!("  }} else {{");
    println!("    // Invalid password");
    println!("  }}");

    let domain = StringLengthDomain::new();

    // 1. Initial state: password is unknown (Top)
    // In StringLengthDomain, Top means length is [0, +∞] (implicitly)
    // But IntervalDomain::top() is [-∞, +∞]. Lengths can't be negative.
    // So we should probably start with length >= 0.

    let mut state = domain.top();

    // Refine: length of password must be >= 0
    let non_neg = NumExpr::var("password").ge(NumExpr::constant(0));
    state = domain.assume_length(&state, &non_neg);
    println!("\nInitial State (after input):");
    println!("  len(password) = {}", domain.get_length(&state, "password"));

    // 2. Branch: if (len(password) >= 8)
    println!("\n--- Analyzing Branch: if (len(password) >= 8) ---");

    let cond = NumExpr::var("password").ge(NumExpr::constant(8));

    // True branch
    let true_branch = domain.assume_length(&state, &cond);
    println!("True Branch (Valid):");
    println!("  len(password) = {}", domain.get_length(&true_branch, "password"));

    // False branch (Negation of condition)
    let false_cond = cond.clone().not();
    let false_branch = domain.assume_length(&state, &false_cond);
    println!("False Branch (Invalid):");
    println!("  len(password) = {}", domain.get_length(&false_branch, "password"));

    // 3. Check properties
    println!("\n--- Verification Results ---");

    // In true branch, is length >= 8?
    let true_len = domain.get_length(&true_branch, "password");
    // We expect [8, +inf]
    assert_eq!(true_len.low, Bound::Finite(8), "Lower bound should be 8");
    assert_eq!(true_len.high, Bound::PosInf, "Upper bound should be infinite");
    println!("  ✓ Verified: Password length is at least 8 in valid branch.");

    // In false branch, is length < 8?
    let false_len = domain.get_length(&false_branch, "password");
    // We expect [0, 7]
    assert_eq!(false_len.low, Bound::Finite(0), "Lower bound should be 0");
    assert_eq!(false_len.high, Bound::Finite(7), "Upper bound should be 7");
    println!("  ✓ Verified: Password length is strictly less than 8 in invalid branch.");

    // Additional check: ensure false branch does not contain 8
    assert!(!false_len.contains(8));

    println!("\n");
}
