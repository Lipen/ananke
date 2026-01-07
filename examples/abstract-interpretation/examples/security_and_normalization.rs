//! Security and Normalization Analysis Example.
//!
//! This example demonstrates three specialized string domains for security and validation:
//!
//! 1. **Taint Analysis (SQL Injection)**:
//!    - Tracks whether data is "Safe" (trusted) or "Tainted" (untrusted user input).
//!    - Proves that sensitive sinks (like SQL execution) only receive Safe data.
//!
//! 2. **String Case Analysis**:
//!    - Tracks the casing of strings (Lowercase, Uppercase, Mixed).
//!    - Useful for ensuring normalization before comparison (e.g., case-insensitive usernames).
//!
//! 3. **Numeric String Analysis**:
//!    - Determines if a string represents a valid number (Integer, Float).
//!    - Useful for pre-validation before parsing to avoid runtime errors.

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::string_domain::{StringCase, StringCaseDomain, StringNumeric, StringNumericDomain, TaintDomain};

fn main() {
    env_logger::init();
    println!("=== Security and Normalization Analysis ===\n");

    example_sql_injection();
    example_normalization();
    example_numeric_input();
}

fn example_sql_injection() {
    println!("Example 1: Taint Analysis (SQL Injection)");
    println!("-----------------------------------------");
    let domain = TaintDomain;

    // Scenario: User input vs Constant query
    // TaintDomain::taint() returns Tainted (Top)
    let user_input = domain.taint();
    // TaintDomain::sanitize() returns Safe
    let query_part = domain.sanitize();

    println!("User Input: {:?}", user_input);
    println!("Query Part: {:?}", query_part);

    // Concatenation: Safe + Tainted = Tainted
    // Any tainted component infects the whole string.
    let unsafe_query = domain.concat(&query_part, &user_input);
    println!("Query + Input: {:?}", unsafe_query);

    if domain.is_top(&unsafe_query) {
        println!("→ ALERT: Potential SQL Injection detected! Query is tainted.");
    } else {
        println!("→ Query is safe.");
    }
    // Assertion: The query should be tainted because user input was used directly.
    assert!(domain.is_top(&unsafe_query), "Expected unsafe query to be tainted");

    // Sanitization
    // Explicitly sanitizing the input makes it Safe.
    let sanitized_input = domain.sanitize();
    // Safe + Safe = Safe
    let safe_query = domain.concat(&query_part, &sanitized_input);
    println!("Query + Sanitized Input: {:?}", safe_query);

    if domain.is_top(&safe_query) {
        println!("→ ALERT: Potential SQL Injection detected!");
    } else {
        println!("→ Query is safe.");
    }
    // Assertion: The query should be safe after sanitization.
    assert!(!domain.is_top(&safe_query), "Expected sanitized query to be safe");
    println!("\n");
}

fn example_normalization() {
    println!("Example 2: String Case Analysis (Normalization)");
    println!("-----------------------------------------------");
    let domain = StringCaseDomain;

    let inputs = vec!["user", "USER", "User", "123"];

    for input in inputs {
        let abs = domain.from_string(input);
        println!("Input '{}': {:?}", input, abs);

        match abs {
            StringCase::Lowercase => {
                println!("→ Already normalized (lowercase).");
                if input == "user" {
                    assert_eq!(abs, StringCase::Lowercase);
                }
                if input == "123" {
                    assert_eq!(abs, StringCase::Lowercase);
                } // Numbers are treated as lower/neutral
            }
            StringCase::Uppercase => {
                println!("→ Needs lowercasing.");
                if input == "USER" {
                    assert_eq!(abs, StringCase::Uppercase);
                }
            }
            StringCase::Mixed => {
                println!("→ Needs normalization.");
                if input == "User" {
                    assert_eq!(abs, StringCase::Mixed);
                }
            }
            _ => {}
        }
    }
    println!();
}

fn example_numeric_input() {
    println!("Example 3: Numeric String Analysis");
    println!("----------------------------------");
    let domain = StringNumericDomain;

    let inputs = vec!["123", "-50", "3.14", "abc", "12ab"];

    for input in inputs {
        let abs = domain.from_string(input);
        println!("Input '{}': {:?}", input, abs);

        match abs {
            StringNumeric::IntegerStr => {
                println!("→ Valid Integer. Safe to parse as int.");
                assert!(input.parse::<i64>().is_ok());
                assert!(input == "123" || input == "-50", "Unexpected IntegerStr for {}", input);
            }
            StringNumeric::FloatStr => {
                println!("→ Valid Float. Safe to parse as float.");
                assert!(input.parse::<f64>().is_ok());
                assert!(input == "3.14", "Unexpected FloatStr for {}", input);
            }
            StringNumeric::Top => {
                println!("→ Invalid or Unknown. Do NOT parse blindly.");
                // "abc" and "12ab" should fall here
                assert!(input.parse::<f64>().is_err());
                assert!(input == "abc" || input == "12ab", "Unexpected Top for {}", input);
            }
            _ => {}
        }
    }
    println!("\n");
}
