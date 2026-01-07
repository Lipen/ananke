//! String Suffix and Inclusion Analysis Example.
//!
//! This example demonstrates two more specialized string domains:
//!
//! 1. **String Suffix Domain**:
//!    - Tracks the common suffix of all possible string values.
//!    - **Application**: File extension validation (e.g., ensuring a file ends with ".pdf").
//!    - **Logic**: `Join("a.doc", "b.doc")` → Suffix(".doc").
//!
//! 2. **String Inclusion Domain**:
//!    - Tracks a set of substrings that *must* be present in the string.
//!    - **Application**: SQL injection prevention (ensuring structure) or required field checks.
//!    - **Logic**: `Join("Hello World", "Hello User")` → MustContain({"Hello"}).
//!    - Useful for verifying that a constructed query always contains "WHERE" or "SELECT".

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::string_domain::{StringInclusionDomain, StringSuffix, StringSuffixDomain};

fn main() {
    env_logger::init();
    println!("=== More Advanced String Analysis ===");
    println!("Demonstrating String Suffix and String Inclusion domains.\n");

    test_suffix_analysis();
    test_inclusion_analysis();
}

fn test_suffix_analysis() {
    println!("--- Part 1: Suffix Analysis (File Extension Validation) ---");
    let domain = StringSuffixDomain;

    println!("Program:");
    println!("  file1 = \"document.pdf\"");
    println!("  file2 = \"image.png\"");
    println!("  file3 = \"script.sh\"");
    println!("  // We want to check if files are safe (e.g. not .sh or .exe)");

    let f1 = StringSuffix::Suffix("document.pdf".to_string());
    let f2 = StringSuffix::Suffix("image.png".to_string());
    let f3 = StringSuffix::Suffix("script.sh".to_string());

    println!("\nAnalysis Results:");
    println!("  File 1 Suffix: {:?}", f1);
    println!("  File 2 Suffix: {:?}", f2);
    println!("  File 3 Suffix: {:?}", f3);

    // Define safe extensions
    let safe_pdf = StringSuffix::Suffix(".pdf".to_string());
    let safe_png = StringSuffix::Suffix(".png".to_string());

    fn is_safe(d: &StringSuffixDomain, s: &StringSuffix, safe_list: &[StringSuffix]) -> bool {
        safe_list.iter().any(|safe| d.le(s, safe))
    }

    let safe_list = vec![safe_pdf, safe_png];

    if is_safe(&domain, &f1, &safe_list) {
        println!("  ✓ Verified: File 1 is safe (.pdf)");
    } else {
        println!("  ✗ Failed: File 1 is unsafe");
    }
    assert!(is_safe(&domain, &f1, &safe_list));

    if is_safe(&domain, &f3, &safe_list) {
        println!("  ✓ Verified: File 3 is safe");
    } else {
        println!("  ✗ Verified: File 3 is unsafe (.sh)");
    }
    assert!(!is_safe(&domain, &f3, &safe_list));

    // Join: Uploading either PDF or PNG
    println!("\n--- Branching Analysis ---");
    println!("Program:");
    println!("  if (cond) file = \"doc.pdf\"");
    println!("  else      file = \"img.png\"");
    println!("  joined = join(branch1, branch2)");

    let joined = domain.join(&f1, &f2);
    println!("\nAnalysis Results:");
    println!("  Joined Suffix: {:?}", joined);
    // LCSuf("document.pdf", "image.png") → empty string? No.
    // "pdf" vs "png" → no common suffix.
    // Wait, "document.pdf" and "image.png".
    // Reverse: "fdp.tnemucod", "gnp.egami".
    // No common prefix in reverse. So suffix is empty.

    // Let's try something with common suffix
    let f4 = StringSuffix::Suffix("report.doc".to_string());
    let f5 = StringSuffix::Suffix("thesis.doc".to_string());
    let joined_doc = domain.join(&f4, &f5);
    println!("  Joined (.doc files): {:?}", joined_doc);
    assert_eq!(joined_doc, StringSuffix::Suffix(".doc".to_string()));
    println!("  ✓ Verified: Common suffix is '.doc'");
}

fn test_inclusion_analysis() {
    println!("\n--- Part 2: Inclusion Analysis (Required Content) ---");
    let domain = StringInclusionDomain;

    println!("Program:");
    println!("  query_part1 = \"SELECT * FROM users\"");
    println!("  query_part2 = \" WHERE id = 1\"");
    println!("  full_query = query_part1 + query_part2");
    println!("  check(full_query contains \"SELECT\")");
    println!("  check(full_query contains \"WHERE\")");

    // In reality, we would analyze the string literal "SELECT * FROM users"
    // and extract all interesting substrings. Here we manually abstract.

    let q1 = domain.from_string("SELECT");
    let q2 = domain.from_string("WHERE");

    let full_query = domain.concat(&q1, &q2);

    println!("\nAnalysis Results:");
    println!("  Part 1 includes: {:?}", q1);
    println!("  Part 2 includes: {:?}", q2);
    println!("  Full Query includes: {:?}", full_query);

    let required = domain.from_string("SELECT");

    // Check if full_query ≤ required (meaning full_query MUST contain "SELECT")
    // Lattice order: Included(A) ≤ Included(B) if B ⊆ A.
    // Here A = {SELECT, WHERE}, B = {SELECT}. {SELECT} is subset of {SELECT, WHERE}.
    // So Included({SELECT, WHERE}) ≤ Included({SELECT}).

    if domain.le(&full_query, &required) {
        println!("  ✓ Verified: Query contains 'SELECT'");
    } else {
        println!("  ✗ Failed: Query might not contain 'SELECT'");
    }
    assert!(domain.le(&full_query, &required));

    // Branching
    println!("\n--- Branching Analysis ---");
    println!("Program:");
    println!("  if (cond) msg = \"Hello World\"");
    println!("  else      msg = \"Hello User\"");
    println!("  joined = join(branch1, branch2)");

    let m1 = domain.from_string("Hello");
    let m2 = domain.from_string("Hello");

    // Let's say m1 also has "World" and m2 has "User"
    let m1_full = domain.concat(&m1, &domain.from_string("World"));
    let m2_full = domain.concat(&m2, &domain.from_string("User"));

    let joined = domain.join(&m1_full, &m2_full);
    println!("\nAnalysis Results:");
    println!("  Branch 1: {:?}", m1_full);
    println!("  Branch 2: {:?}", m2_full);
    println!("  Joined:   {:?}", joined);

    // Intersection of {Hello, World} and {Hello, User} is {Hello}
    if domain.le(&joined, &domain.from_string("Hello")) {
        println!("  ✓ Verified: Result always contains 'Hello'");
    } else {
        println!("  ✗ Failed");
    }
    assert!(domain.le(&joined, &domain.from_string("Hello")));

    if !domain.le(&joined, &domain.from_string("World")) {
        println!("  ✓ Verified: Result does NOT guarantee 'World'");
    } else {
        println!("  ✗ Failed");
    }
    assert!(!domain.le(&joined, &domain.from_string("World")));
}
