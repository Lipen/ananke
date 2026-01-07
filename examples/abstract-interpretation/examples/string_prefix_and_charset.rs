//! String Prefix and Character Set Analysis Example.
//!
//! This example demonstrates two specialized string domains for security analysis:
//!
//! 1. **String Prefix Domain**:
//!    - Tracks the common prefix of all possible string values.
//!    - **Application**: Protocol validation (e.g., ensuring a URL starts with "https://").
//!    - **Logic**: `Join("http://a", "https://b")` → Prefix("http").
//!
//! 2. **Character Set Domain**:
//!    - Tracks the set of characters that *may* appear in the string.
//!    - **Application**: Input sanitization (e.g., ensuring a string contains only digits).
//!    - **Logic**: `Join("123", "45a")` → CharSet({'1','2','3','4','5','a'}).
//!    - Allows verifying "is_numeric" properties by checking subset relationships.

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::string_domain::{CharacterSet, CharacterSetDomain, StringPrefix, StringPrefixDomain};

fn main() {
    env_logger::init();
    println!("=== Advanced String Analysis ===");
    println!("Demonstrating String Prefix and Character Set domains.\n");

    test_prefix_analysis();
    test_charset_analysis();
}

fn test_prefix_analysis() {
    println!("--- Part 1: Prefix Analysis (URL Validation) ---");
    let domain = StringPrefixDomain;

    println!("Program:");
    println!("  protocol = \"https://\"");
    println!("  domain = \"example.com\"");
    println!("  url = protocol + domain");

    // Scenario: Constructing a URL
    // url = "https://" + "example.com"
    let protocol = StringPrefix::Prefix("https://".to_string());
    let domain_part = StringPrefix::Prefix("example.com".to_string());

    println!("\nAnalysis Results:");
    println!("  Protocol: {:?}", protocol);
    println!("  Domain:   {:?}", domain_part);

    let url = domain.concat(&protocol, &domain_part);
    println!("  Full URL Prefix: {:?}", url);

    // Check if it is a secure URL
    let secure_prefix = StringPrefix::Prefix("https".to_string());
    assert!(domain.le(&url, &secure_prefix));
    println!("  ✓ Verified: URL starts with 'https'");

    // Branching:
    println!("\n--- Branching Analysis ---");
    println!("Program:");
    println!("  if (cond) url = \"http://...\"");
    println!("  else      url = \"https://...\"");
    println!("  joined = join(branch1, branch2)");

    let http = StringPrefix::Prefix("http://".to_string());
    let https = StringPrefix::Prefix("https://".to_string());

    let joined = domain.join(&http, &https);
    println!("\nAnalysis Results:");
    println!("  Joined (Branch Result): {:?}", joined);

    // Expect "http" (LCP of http:// and https://)
    assert_eq!(joined, StringPrefix::Prefix("http".to_string()));
    println!("  ✓ Verified: Common prefix is 'http'");
}

fn test_charset_analysis() {
    println!("\n--- Part 2: Character Set Analysis (Sanitization) ---");
    let domain = CharacterSetDomain;

    println!("Program:");
    println!("  input1 = \"123\"");
    println!("  input2 = \"45a\"");
    println!("  joined = join(input1, input2)");
    println!("  check(is_numeric(input1))");
    println!("  check(is_numeric(joined))");

    // Input 1: "123"
    let input1 = domain.from_string("123");

    // Input 2: "45a"
    let input2 = domain.from_string("45a");

    // Join (Union)
    let joined = domain.join(&input1, &input2);

    println!("\nAnalysis Results:");
    println!("  Input 1 chars: {:?}", input1);
    println!("  Input 2 chars: {:?}", input2);
    println!("  Joined chars:  {:?}", joined);

    // Check if numeric
    let digits = domain.from_string("0123456789");

    fn is_numeric(d: &CharacterSetDomain, val: &CharacterSet, digits: &CharacterSet) -> bool {
        d.le(val, digits)
    }

    assert!(is_numeric(&domain, &input1, &digits));
    println!("  ✓ Verified: Input 1 is numeric");

    assert!(!is_numeric(&domain, &joined, &digits));
    println!("  ✓ Verified: Joined input is NOT numeric (contains 'a')");
}
