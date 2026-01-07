//! Symbolic Automata Domain Analysis Example
//!
//! This example demonstrates how to use the `AutomataDomain` for string analysis.
//! We model different string formats using symbolic automata and analyze their properties
//! using abstract domain operations: join (union), meet (intersection), and subset checking.
//!
//! ## String Languages Being Analyzed
//!
//! 1. **Identifiers**: `[a-zA-Z_][a-zA-Z0-9_]*`
//!    - Valid: "my_var", "_private", "var123"
//!    - Invalid: "123var" (starts with digit), "$invalid" (special char)
//!
//! 2. **Integers**: `[0-9]+`
//!    - Valid: "123", "0", "999"
//!    - Invalid: "12a" (contains letter)
//!
//! ## Analysis Scenarios
//!
//! - **Union (Join)**: Variable that can be *either* an identifier or an integer
//! - **Intersection (Meet)**: Strings that are *both* identifiers and integers (empty!)
//! - **Subset (Le)**: Check if specific strings belong to a language

use abstract_interpretation::*;

fn main() {
    env_logger::init();
    println!("=== Symbolic Automata Domain Analysis ===\n");

    let domain = AutomataDomain;

    // 1. Define basic character classes
    // These are the building blocks for our automata transitions.
    let digit = CharClass::range('0', '9');
    let alpha_lower = CharClass::range('a', 'z');
    let alpha_upper = CharClass::range('A', 'Z');
    let alpha = alpha_lower.or(&alpha_upper);
    let alphanumeric = alpha.or(&digit);
    let underscore = CharClass::single('_');
    let identifier_char = alphanumeric.or(&underscore);

    // ========================================================================
    // Scenario 1: Identifier Language
    // ========================================================================
    // Language being analyzed:
    //   Regex: [a-zA-Z_][a-zA-Z0-9_]*
    //   Examples:
    //     ✓ "my_var", "_private", "var123", "CamelCase"
    //     ✗ "123var" (starts with digit), "$invalid" (special char)
    println!("\n=======================================================");
    println!("Scenario 1: Identifier Language");
    println!("=======================================================\n");

    println!("Program Context:");
    println!("  // Variable 'id' must be a valid identifier");
    println!("  // Regex: [a-zA-Z_][a-zA-Z0-9_]*");
    println!();

    // 2. Construct an automaton for valid identifiers: [a-zA-Z_][a-zA-Z0-9_]*
    println!("Constructing Symbolic Automaton...");
    let mut nfa_ident = SymbolicNFA::new();
    let start = nfa_ident.start; // state 0
    let body = nfa_ident.add_state(true); // state 1 (accepting)

    // Transition: start --[a-zA-Z_]--> body
    // The first character must be a letter or underscore.
    nfa_ident.add_transition(start, alpha.or(&underscore), body);

    // Transition: body --[a-zA-Z0-9_]--> body
    // Subsequent characters can be alphanumeric or underscore.
    nfa_ident.add_transition(body, identifier_char.clone(), body);

    let dfa_ident = nfa_ident.determinize();
    println!("  States: {}", dfa_ident.states);
    println!("  Accepting: {:?}", dfa_ident.accepting);
    println!();

    // Test some strings
    println!("Test Acceptance:");
    let test_cases = [
        ("my_var", true),
        ("_private", true),
        ("var123", true),
        ("CamelCase", true),
        ("123var", false),
        ("$invalid", false),
    ];

    for (input, expected) in &test_cases {
        let result = dfa_ident.accepts(input);
        let mark = if result == *expected { "✓" } else { "✗" };
        println!("  {} '{}' -> {}", mark, input, result);
        assert_eq!(result, *expected, "Unexpected result for '{}'", input);
    }

    // ========================================================================
    // Scenario 2: Integer Language
    // ========================================================================
    // Language being analyzed:
    //   Regex: [0-9]+
    //   Examples:
    //     ✓ "123", "0", "999"
    //     ✗ "12a" (contains letter), "" (empty)
    println!("\n=======================================================");
    println!("Scenario 2: Integer Language");
    println!("=======================================================\n");

    println!("Program Context:");
    println!("  // Variable 'num' must be an integer literal");
    println!("  // Regex: [0-9]+");
    println!();

    // 3. Construct an automaton for integer literals: [0-9]+
    println!("Constructing Symbolic Automaton...");
    let mut nfa_int = SymbolicNFA::new();
    let start = nfa_int.start;
    let body = nfa_int.add_state(true);

    // Transition: start --[0-9]--> body
    // Must start with a digit.
    nfa_int.add_transition(start, digit.clone(), body);

    // Transition: body --[0-9]--> body
    // Can continue with digits.
    nfa_int.add_transition(body, digit.clone(), body);

    let dfa_int = nfa_int.determinize();
    println!("  States: {}", dfa_int.states);
    println!("  Accepting: {:?}", dfa_int.accepting);
    println!();

    println!("Test Acceptance:");
    let test_cases = [("123", true), ("0", true), ("999", true), ("12a", false), ("", false)];

    for (input, expected) in &test_cases {
        let result = dfa_int.accepts(input);
        let mark = if result == *expected { "✓" } else { "✗" };
        println!("  {} '{}' -> {}", mark, input, result);
        assert_eq!(result, *expected, "Unexpected result for '{}'", input);
    }

    // ========================================================================
    // Scenario 3: Union (Join) - Identifier OR Integer
    // ========================================================================
    // Analysis question: What if a variable can be either an identifier or an integer?
    println!("\n=======================================================");
    println!("Scenario 3: Union (Join) - Identifier OR Integer");
    println!("=======================================================\n");

    // 4. Analyze a scenario:
    // Let's say we have a variable `x` that can be either an identifier OR an integer.
    // We want to compute the abstract state for `x`.
    println!("Computing: Identifier ⊔ Integer");
    println!("Description: Strings that are EITHER identifiers OR integers\n");

    let state_x = domain.join(&dfa_ident, &dfa_int);

    println!("Result:");
    println!("  States: {}", state_x.states);
    println!();

    println!("Test Acceptance:");
    let test_cases = [
        ("var1", true, "identifier"),
        ("99", true, "integer"),
        ("_private", true, "identifier"),
        ("$invalid", false, "neither"),
        ("12a", false, "neither"),
    ];

    for (input, expected, desc) in &test_cases {
        let result = state_x.accepts(input);
        let mark = if result == *expected { "✓" } else { "✗" };
        println!("  {} '{}' -> {} ({})", mark, input, result, desc);
        assert_eq!(
            result,
            *expected,
            "Union should {} '{}'",
            if *expected { "accept" } else { "reject" },
            input
        );
    }

    // ========================================================================
    // Scenario 4: Intersection (Meet) - Identifier AND Integer
    // ========================================================================
    // Analysis question: What strings are BOTH identifiers AND integers?
    println!("\n=======================================================");
    println!("Scenario 4: Intersection (Meet) - Identifier AND Integer");
    println!("=======================================================\n");

    // 5. Intersection (Meet)
    // What strings are BOTH identifiers AND integers?
    // Ideally this should be empty because identifiers can't start with a digit,
    // and integers must consist only of digits.
    println!("Computing: Identifier ⊓ Integer");
    println!("Description: Strings that are BOTH identifiers AND integers");
    println!("Expected: Empty (Bottom) - languages are disjoint\n");

    let intersection = domain.meet(&dfa_ident, &dfa_int);

    println!("Result:");
    println!("  Is Bottom? {}", domain.is_bottom(&intersection));
    assert!(
        domain.is_bottom(&intersection),
        "Intersection of disjoint languages should be empty"
    );
    println!("  ✓ Verified: Intersection is empty (as expected)\n");

    println!("Explanation:");
    println!("  - Identifiers start with [a-zA-Z_]");
    println!("  - Integers start with [0-9]");
    println!("  - These character sets are disjoint → no string can be both");

    // ========================================================================
    // Scenario 5: Subset (Le) - Singleton Language
    // ========================================================================
    // Analysis question: Is a specific string in a language?
    println!("\n=======================================================");
    println!("Scenario 5: Subset Checking - Singleton Languages");
    println!("=======================================================\n");

    // 6. Subset Check (Le)
    println!("Language: {{\"var1\"}} (singleton)");
    println!("Description: Language containing only the string \"var1\"\n");

    println!("Constructing Symbolic Automaton...");
    // "var1" is a specific identifier. Let's make a singleton DFA.
    let mut nfa_var1 = SymbolicNFA::new();
    let s0 = 0;
    let s1 = nfa_var1.add_state(false);
    let s2 = nfa_var1.add_state(false);
    let s3 = nfa_var1.add_state(false);
    let s4 = nfa_var1.add_state(true);

    nfa_var1.add_transition(s0, CharClass::single('v'), s1);
    nfa_var1.add_transition(s1, CharClass::single('a'), s2);
    nfa_var1.add_transition(s2, CharClass::single('r'), s3);
    nfa_var1.add_transition(s3, CharClass::single('1'), s4);

    let dfa_var1 = nfa_var1.determinize();
    println!("  States: {}", dfa_var1.states);
    println!();

    println!("Subset Queries:");

    let is_subset = domain.le(&dfa_var1, &dfa_ident);
    println!("  {{\"var1\"}} ⊆ Identifiers? {}", is_subset);
    assert!(is_subset, "\"var1\" should be an identifier");
    println!("    ✓ Verified: \"var1\" is a valid identifier");

    let is_subset_int = domain.le(&dfa_var1, &dfa_int);
    println!("\n  {{\"var1\"}} ⊆ Integers? {}", is_subset_int);
    assert!(!is_subset_int, "\"var1\" should not be an integer");
    println!("    ✓ Verified: \"var1\" is not an integer");

    println!("\n=======================================================");
    println!("Analysis Complete - All Assertions Passed!");
    println!("=======================================================");
}
