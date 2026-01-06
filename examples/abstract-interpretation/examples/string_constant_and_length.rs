//! String Constant and Length Analysis Example.
//!
//! This example demonstrates two fundamental string abstract domains:
//!
//! 1. **String Constant Domain**:
//!    - Tracks exact string values (e.g., `s = "hello"`).
//!    - Becomes `Top` (Unknown) if the string can have multiple values (e.g., after a merge).
//!    - Useful for constant propagation and precise equality checks.
//!
//! 2. **String Length Domain**:
//!    - Tracks the length of strings as an interval (e.g., `len(s) ∈ [5, 10]`).
//!    - Useful for buffer overflow detection and loop termination analysis.
//!    - Can prove properties like "string length grows indefinitely" in a loop.

use abstract_interpretation::domain::AbstractDomain;
use abstract_interpretation::{Interval, StringConst, StringConstantDomain, StringLengthDomain};

fn main() {
    println!("=== String Analysis Example ===");
    println!("This example demonstrates two string abstract domains:");
    println!("1. String Constant Domain: Tracks exact string values.");
    println!("2. String Length Domain: Tracks the length of strings using intervals.");

    // 1. String Constant Analysis
    println!("\n--- Part 1: String Constant Domain ---");
    println!("Program being analyzed:");
    println!("  s1 = \"hello\"");
    println!("  s2 = \"world\"");
    println!("  s3 = \"hello\"");
    println!("  joined1 = join(s1, s2)");
    println!("  joined2 = join(s1, s3)");

    let const_domain = StringConstantDomain;

    let s1 = StringConst::Constant("hello".to_string());
    let s2 = StringConst::Constant("world".to_string());
    let s3 = StringConst::Constant("hello".to_string());

    println!("\nAnalysis Results:");
    println!("  s1: {:?}", s1);
    println!("  s2: {:?}", s2);
    println!("  s3: {:?}", s3);

    let joined = const_domain.join(&s1, &s2);
    println!("  join(s1, s2):   {:?}", joined);
    println!("    -> 'join' merges control paths: value is 'hello' OR 'world' -> Unknown");
    assert_eq!(joined, StringConst::Top);

    let concatenated = const_domain.concat(&s1, &s2);
    println!("  concat(s1, s2): {:?}", concatenated);
    println!("    -> 'concat' combines values: value is 'hello' + 'world'");
    assert_eq!(concatenated, StringConst::Constant("helloworld".to_string()));

    let joined_same = const_domain.join(&s1, &s3);
    println!("  join(s1, s3):   {:?}", joined_same);
    println!("    -> Values match, so result is precise");
    assert_eq!(joined_same, StringConst::Constant("hello".to_string())); // 2. String Length Analysis
    println!("\n--- Part 2: String Length Domain ---");
    println!("Program being analyzed:");
    println!("  s1 = \"abc\"");
    println!("  s2 = \"defg\"");
    println!("  s3 = s1 + s2");

    let len_domain = StringLengthDomain::new();
    let mut state = len_domain.top();

    println!("\nAnalysis Trace:");

    // s1 = "abc"
    state = len_domain.assign_const(&state, "s1", "abc");
    let len_s1 = len_domain.get_length(&state, "s1");
    println!("  After s1 = \"abc\":      len(s1) = {}", len_s1);

    // s2 = "defg"
    state = len_domain.assign_const(&state, "s2", "defg");
    let len_s2 = len_domain.get_length(&state, "s2");
    println!("  After s2 = \"defg\":     len(s2) = {}", len_s2);

    // s3 = s1 + s2
    state = len_domain.assign_concat(&state, "s3", "s1", "s2");
    let len_s3 = len_domain.get_length(&state, "s3");
    println!("  After s3 = s1 + s2:    len(s3) = {}", len_s3);
    assert_eq!(len_s3, Interval::constant(7));

    // Loop simulation: s = "a"; while (*) s = s + "b";
    println!("\n--- Part 3: Loop Analysis ---");
    println!("Program being analyzed:");
    println!("  s = \"a\";");
    println!("  while (unknown) {{");
    println!("    s = s + \"b\";");
    println!("  }}");

    let mut loop_state = len_domain.top();
    loop_state = len_domain.assign_const(&loop_state, "s", "a");

    println!("\nFixpoint Iteration:");
    println!("  Init: len(s) = {}", len_domain.get_length(&loop_state, "s"));

    for i in 1..=5 {
        // Body: s_new = s_old + "b"
        // s_temp = "b"
        let temp_state = len_domain.assign_const(&loop_state, "temp", "b");
        // s_next = s + temp
        let next_state = len_domain.assign_concat(&temp_state, "s_next", "s", "temp");

        // Join with previous state (s = s ⊔ s_next)
        let s_next_len = len_domain.get_length(&next_state, "s_next");
        let current_s_len = len_domain.get_length(&loop_state, "s");

        // Use widening to ensure termination
        let new_s_len = current_s_len.widen(&s_next_len);

        println!("  Iter {}: s_next len = {}, widened = {}", i, s_next_len, new_s_len);

        let old_len = len_domain.get_length(&loop_state, "s");
        loop_state.set("s", new_s_len);

        if old_len == new_s_len {
            println!("  Convergence reached at iteration {}!", i);
            break;
        }
    }

    println!("\nFinal Result:");
    println!("  len(s) = {}", len_domain.get_length(&loop_state, "s"));
    println!("  Interpretation: The string length starts at 1 and can grow indefinitely.");
}
