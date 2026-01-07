//! String Concatenation Analysis Example.
//!
//! This example demonstrates how the **String Length Domain** tracks string lengths
//! through concatenation operations.
//!
//! Scenario:
//! Constructing a URL from fixed parts (protocol, domain) and variable parts (query string).
//!
//! The analysis computes:
//! - Exact lengths for constant strings.
//! - Precise length ranges for concatenated strings (e.g., `len(A + B) = len(A) + len(B)`).
//!
//! This allows verifying properties like "URL length never exceeds buffer size" even
//! when the exact string content is unknown.

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::{Bound, Interval, NumExpr, StringLengthDomain};

fn main() {
    env_logger::init();
    println!("=== String Concatenation Analysis ===\n");

    println!("This example demonstrates analyzing string lengths during concatenation.");
    println!("Scenario: Constructing a URL from parts and verifying its length.");

    let domain = StringLengthDomain::new();
    let mut state = domain.top();

    // 1. Define parts of a URL
    println!("\n--- Step 1: Define URL Parts ---");
    println!("Program:");
    println!("  protocol = \"https://\"");
    println!("  domain = \"example.com\"");
    println!("  path = \"/api/v1\"");

    // protocol = "https://" (len 8)
    state = domain.assign_const(&state, "protocol", "https://");

    // domain = "example.com" (len 11)
    state = domain.assign_const(&state, "domain", "example.com");

    // path = "/api/v1" (len 7)
    state = domain.assign_const(&state, "path", "/api/v1");

    println!("\nAnalysis Results:");
    let len_proto = domain.get_length(&state, "protocol");
    println!("  len(protocol): {}", len_proto);
    assert_eq!(len_proto, Interval::constant(8));

    let len_domain_var = domain.get_length(&state, "domain");
    println!("  len(domain):   {}", len_domain_var);
    assert_eq!(len_domain_var, Interval::constant(11));

    let len_path = domain.get_length(&state, "path");
    println!("  len(path):     {}", len_path);
    assert_eq!(len_path, Interval::constant(7));

    // 2. Build full URL
    println!("\n--- Step 2: Build Full URL ---");
    println!("Program:");
    println!("  url = protocol + domain + path");

    // url = protocol + domain
    state = domain.assign_concat(&state, "temp", "protocol", "domain");
    // url = temp + path
    state = domain.assign_concat(&state, "url", "temp", "path");

    let url_len = domain.get_length(&state, "url");
    println!("\nAnalysis Results:");
    println!("  len(url): {}", url_len);

    // Expected length: 8 + 11 + 7 = 26
    assert_eq!(url_len, Interval::constant(26));
    println!("  ✓ Verified: URL length is exactly 26."); // 3. Variable length part
    println!("\n--- Step 3: Variable Length Analysis ---");
    println!("Program:");
    println!("  assume(0 ≤ len(query) ≤ 100)");
    println!("  full_url = url + query");

    // query = input() (assume length 0 to 100)
    let query_len_pred = NumExpr::var("query")
        .ge(NumExpr::constant(0))
        .and(NumExpr::var("query").le(NumExpr::constant(100)));
    state = domain.assume_length(&state, &query_len_pred);
    println!("\nAnalysis Results:");
    println!("  len(query): {}", domain.get_length(&state, "query"));

    // full_url = url + query
    state = domain.assign_concat(&state, "full_url", "url", "query");

    let full_len = domain.get_length(&state, "full_url");
    println!("  len(full_url): {}", full_len);

    // Expected: [26, 126]
    assert_eq!(full_len, Interval::new(Bound::Finite(26), Bound::Finite(126)));
    println!("  ✓ Verified: Full URL length ∈ [26, 126].");

    if let (Bound::Finite(l), Bound::Finite(h)) = (full_len.low, full_len.high) {
        assert!(l >= 26);
        assert!(h <= 126);
    } else {
        panic!("Expected finite bounds for full URL length");
    }
}
