//! Regex Domain Analysis Example.
//!
//! This example demonstrates the **Regex Domain**, which tracks the structure
//! of string values using Regular Expressions.
//!
//! Applications:
//! - **Input Validation**: Verifying that strings match a specific format (e.g., email, ID).
//! - **Structured Logging**: Ensuring log messages follow a consistent pattern.
//! - **Data Sanitization**: Checking if output contains sensitive patterns.

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::string_domain::{RegexDomain, StringRegex};
use regex::Regex;

fn main() {
    env_logger::init();
    println!("=== Regex Domain Analysis ===\n");

    test_id_generation();
    println!("{}", "─".repeat(60));
    test_structured_logging();

    println!("\n=======================================================");
    println!("   Analysis Complete");
    println!("=======================================================\n");
}

fn test_id_generation() {
    println!("--- Part 1: ID Generation Analysis ---");
    let domain = RegexDomain::default();

    println!("Program:");
    println!("  prefix = \"USER-\"");
    println!("  id_part = \"[0-9]+\" (abstracted)");
    println!("  full_id = prefix + id_part");

    // 1. Define parts
    // prefix = "USER-"
    let prefix = domain.from_string("USER-");

    // id_part = [0-9]+
    // In a real analysis, this might come from analyzing a random number generator
    // or an integer-to-string conversion. Here we assume we inferred this pattern.
    let id_part = domain.from_pattern("[0-9]+");

    println!("\nAnalysis Results:");
    println!("  Prefix: {:?}", prefix);
    println!("  ID Part: {:?}", id_part);

    // 2. Concatenate
    let full_id = domain.concat(&prefix, &id_part);
    println!("  Full ID: {:?}", full_id);

    // Verify against concrete examples
    if let StringRegex::Regex(pattern) = full_id {
        println!("  → Generated Regex: {}", pattern);

        // Verify with 'regex' crate
        // Note: We need to anchor it to ensure full match for this test
        let re = Regex::new(&format!("^{}$", pattern)).expect("Invalid regex generated");

        let valid_id = "USER-12345";
        let invalid_id = "ADMIN-12345";

        assert!(re.is_match(valid_id));
        println!("  ✓ Verified: Matches '{}'", valid_id);

        assert!(!re.is_match(invalid_id));
        println!("  ✓ Verified: Does NOT match '{}'", invalid_id);
    } else {
        println!("  Result is Top or Bottom");
        panic!("Expected a specific Regex pattern, got Top or Bottom");
    }
}

fn test_structured_logging() {
    println!("\n--- Part 2: Structured Logging Analysis (Branching) ---");
    let domain = RegexDomain::default();

    println!("Program:");
    println!("  if (is_admin) {{");
    println!("    type = \"ADMIN\"");
    println!("  }} else {{");
    println!("    type = \"USER\"");
    println!("  }}");
    println!("  log = \"[\" + type + \"] Login successful\"");

    // Branch 1: type = "ADMIN"
    let type_admin = domain.from_string("ADMIN");

    // Branch 2: type = "USER"
    let type_user = domain.from_string("USER");

    // Join branches
    let type_joined = domain.join(&type_admin, &type_user);
    println!("\nAnalysis Results:");
    println!("  Type (Joined): {:?}", type_joined);

    // Construct log message
    // log = "[" + type + "] Login successful"
    let bracket_open = domain.from_string("[");
    let bracket_close = domain.from_string("] Login successful");

    let temp = domain.concat(&bracket_open, &type_joined);
    let log_msg = domain.concat(&temp, &bracket_close);

    println!("  Log Message: {:?}", log_msg);

    if let StringRegex::Regex(pattern) = log_msg {
        println!("  → Generated Regex: {}", pattern);

        let re = Regex::new(&format!("^{}$", pattern)).expect("Invalid regex generated");

        let log1 = "[ADMIN] Login successful";
        let log2 = "[USER] Login successful";
        let log3 = "[GUEST] Login successful";

        assert!(re.is_match(log1));
        println!("  ✓ Verified: Matches '{}'", log1);

        assert!(re.is_match(log2));
        println!("  ✓ Verified: Matches '{}'", log2);

        assert!(!re.is_match(log3));
        println!("  ✓ Verified: Does NOT match '{}'", log3);
    } else {
        panic!("Expected a specific Regex pattern for log message");
    }
}
