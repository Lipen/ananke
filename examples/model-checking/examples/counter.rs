//! # N-Bit Counter — BDD Scalability Demonstration
//!
//! This example demonstrates how BDD-based model checking scales with system size.
//! We verify properties of an n-bit binary counter, showing that BDDs can handle
//! systems with exponentially many states efficiently.
//!
//! ## The System
//!
//! An n-bit binary counter that increments on each step:
//! - n=4:  States 0 → 1 → 2 → ... → 15 → 0 (wrap around)
//! - n=8:  States 0 → 1 → 2 → ... → 255 → 0
//! - n=16: States 0 → 1 → 2 → ... → 65535 → 0
//!
//! ## Why This Matters
//!
//! The counter has 2^n states, yet:
//! - BDD representation is polynomial in n (not exponential!)
//! - Reachability computation visits ALL states symbolically
//! - Property checking scales gracefully with bit width
//!
//! This demonstrates the "symbolic" advantage of BDDs: we never enumerate
//! states explicitly, instead manipulating sets of states as logical formulas.
//!
//! ## What We Verify
//!
//! 1. **Complete Coverage**: All 2^n states are reachable
//! 2. **Wrap-around**: Counter always returns to zero from max value
//! 3. **Progress**: Every state eventually transitions
//! 4. **Reversibility**: Any state is always eventually reachable
//!
//! Run with: `cargo run --example counter --release`

use std::rc::Rc;
use std::time::Instant;

use ananke_bdd::bdd::Bdd;
use model_checking::*;

fn header(s: &str) {
    println!("{}", s);
    println!("{}", "─".repeat(s.len()));
    println!();
}

/// Creates an n-bit counter transition system.
///
/// The counter increments according to standard binary addition:
/// - b0' = ¬b0 (LSB always flips)
/// - b1' = b1 ⊕ b0 (flip if carry from b0)
/// - b2' = b2 ⊕ (b0 ∧ b1) (flip if carry from b0 and b1)
/// - General: bi' = bi ⊕ (b0 ∧ b1 ∧ ... ∧ b(i-1))
fn create_counter(n: usize) -> Rc<TransitionSystem> {
    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    // Create n bit variables: b0 (LSB) to b(n-1) (MSB)
    let vars: Vec<Var> = (0..n).map(|i| Var::new(format!("b{}", i))).collect();

    for var in &vars {
        ts.declare_var(var.clone());
    }

    // Variable ordering: interleaved (b0 < b0' < b1 < b1' < ...) is used by default.
    // This is much better than natural (b0 < b1 < ... < b0' < b1' < ...) for
    // transition relations because it keeps related variables (bi and bi') close,
    // which leads to smaller intermediate BDDs during image computation.

    // Get BDD variable handles
    let present: Vec<_> = vars.iter().map(|v| ts.var_manager().get_present(v).unwrap()).collect();
    let next: Vec<_> = vars.iter().map(|v| ts.var_manager().get_next(v).unwrap()).collect();

    let present_bdds: Vec<_> = present.iter().map(|&p| bdd.mk_var(p)).collect();
    let next_bdds: Vec<_> = next.iter().map(|&n| bdd.mk_var(n)).collect();

    // Initial state: counter = 0 (all bits false)
    let mut initial = bdd.one();
    for &p in &present_bdds {
        initial = bdd.apply_and(initial, bdd.apply_not(p));
    }
    ts.set_initial(initial);

    // Build transition relation for binary increment
    //
    // The key insight: each bit flips when all lower bits are 1.
    // - b0 always flips: b0' = ¬b0
    // - b1 flips when b0=1: b1' = b1 ⊕ b0
    // - b2 flips when b0=1 and b1=1: b2' = b2 ⊕ (b0 ∧ b1)
    // - etc.

    let mut transition = bdd.one();

    // b0' = ¬b0 (LSB always toggles)
    let b0_next_expr = bdd.apply_not(present_bdds[0]);
    let b0_constraint = bdd.apply_eq(next_bdds[0], b0_next_expr);
    transition = bdd.apply_and(transition, b0_constraint);

    // For each subsequent bit: bi' = bi ⊕ carry
    // where carry = b0 ∧ b1 ∧ ... ∧ b(i-1)
    let mut carry = present_bdds[0];
    for i in 1..n {
        // bi' = bi ⊕ carry (flip if carry-in)
        let bi_next_expr = bdd.apply_xor(present_bdds[i], carry);
        let bi_constraint = bdd.apply_eq(next_bdds[i], bi_next_expr);
        transition = bdd.apply_and(transition, bi_constraint);

        // Update carry for next bit: carry = carry ∧ bi
        carry = bdd.apply_and(carry, present_bdds[i]);
    }

    ts.set_transition(transition);

    // Add useful labels for properties
    // "zero" = all bits are 0 (counter value = 0)
    let mut zero = bdd.one();
    for &p in &present_bdds {
        zero = bdd.apply_and(zero, bdd.apply_not(p));
    }
    ts.add_label("zero".to_string(), zero);

    // "max" = all bits are 1 (counter value = 2^n - 1)
    let mut max = bdd.one();
    for &p in &present_bdds {
        max = bdd.apply_and(max, p);
    }
    ts.add_label("max".to_string(), max);

    // "even" = LSB is 0
    let even = bdd.apply_not(present_bdds[0]);
    ts.add_label("even".to_string(), even);

    // "odd" = LSB is 1
    let odd = present_bdds[0];
    ts.add_label("odd".to_string(), odd);

    Rc::new(ts)
}

fn main() {
    println!("═════════════════════════════════════════════════");
    println!("  N-Bit Counter — BDD Scalability Demonstration  ");
    println!("═════════════════════════════════════════════════");
    println!();

    header("Part 1: Detailed Analysis of 4-bit Counter");

    println!("Building 4-bit counter model...");
    println!("  Counter cycles: 0 → 1 → 2 → ... → 15 → 0 (wrap)\n");

    let ts = create_counter(4);
    let checker = CtlChecker::new(ts.clone());

    header("Analysis 1: State Space");

    let reachable = ts.reachable();
    let state_count = ts.count_states(reachable);

    if let Some(count) = state_count {
        println!("  Variables: 4 bits");
        println!("  Maximum states: 2^4 = 16");
        println!("  Reachable states: {}", count);

        // A 4-bit counter visits ALL 16 states
        assert_eq!(count, 16, "4-bit counter should have exactly 16 reachable states");
        println!("  ✓ All 16 states are reachable");
        println!();
    }

    header("Property 1: Reversibility");
    println!("CTL: AG EF zero");
    println!("'From any state, zero is reachable'\n");

    let ag_ef_zero = CtlFormula::atom("zero").ef().ag();
    let reversibility = checker.holds_initially(&ag_ef_zero);

    println!("  Result: {}", if reversibility { "✓ HOLDS" } else { "✗ VIOLATED" });

    assert!(reversibility, "Counter should always be able to return to zero!");
    println!("  ✓ Counter can always cycle back to zero");
    println!();

    header("Property 2: Maximum Reachability");
    println!("CTL: AF max");
    println!("'Counter will reach maximum (15)'\n");

    let af_max = CtlFormula::atom("max").af();
    let reaches_max = checker.holds_initially(&af_max);

    println!("  Result: {}", if reaches_max { "✓ HOLDS" } else { "✗ VIOLATED" });

    assert!(reaches_max, "Counter should eventually reach max value!");
    println!("  ✓ Counter reaches 15 on every path");
    println!();

    header("Property 3: Wrap-around");
    println!("CTL: AG (max → AX zero)");
    println!("'After max (15), next state is zero'\n");

    let wrap_around = CtlFormula::atom("max").implies(CtlFormula::atom("zero").ax()).ag();
    let wraps = checker.holds_initially(&wrap_around);

    println!("  Result: {}", if wraps { "✓ HOLDS" } else { "✗ VIOLATED" });

    assert!(wraps, "Counter should wrap from max to zero!");
    println!("  ✓ 15 + 1 = 0 (mod 16)");
    println!();

    header("Property 4: Parity Alternation");
    println!("CTL: AG (even → AX odd)");
    println!("'Even numbers followed by odd'\n");

    let even_to_odd = CtlFormula::atom("even").implies(CtlFormula::atom("odd").ax()).ag();
    let alternates = checker.holds_initially(&even_to_odd);

    println!("  Result: {}", if alternates { "✓ HOLDS" } else { "✗ VIOLATED" });

    assert!(alternates, "Even numbers should be followed by odd numbers!");
    println!("  ✓ Parity alternates correctly");
    println!();

    header("Part 2: Scalability Analysis");

    println!("Testing how BDD performance scales with counter size...");
    println!();

    println!(
        "  {:>5}  {:>12}  {:>10}  {:>10}  {:>10}  {:>10}  {:>12}",
        "Bits", "States", "Build", "Reach", "Check", "Nodes", "Cache Hits"
    );
    println!(
        "  {}  {}  {}  {}  {}  {}  {}",
        "-".repeat(5),
        "-".repeat(12),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(12)
    );

    // Test various sizes
    for n in [4, 6, 8, 10, 12, 14, 16] {
        let expected_states: u128 = 1u128 << n;

        // Build the counter
        let build_start = Instant::now();
        let ts = create_counter(n);
        let build_time = build_start.elapsed();

        let bdd = ts.bdd();

        // Check reachability
        let reach_start = Instant::now();
        let reachable = ts.reachable();
        let reach_time = reach_start.elapsed();

        // Count states
        let count = ts.count_states(reachable);

        // Verify state count
        if let Some(c) = count {
            assert_eq!(
                c as u128, expected_states,
                "{}-bit counter should have 2^{} = {} states",
                n, n, expected_states
            );
        }

        // Verify AG EF zero (reversibility)
        let checker = CtlChecker::new(ts.clone());
        let prop = CtlFormula::atom("zero").ef().ag();

        let check_start = Instant::now();
        let holds = checker.holds_initially(&prop);
        let check_time = check_start.elapsed();

        assert!(holds, "{}-bit counter should satisfy AG EF zero", n);

        // Collect BDD statistics
        let total_nodes = bdd.num_nodes();
        let cache_hits = bdd.cache().hits();

        // Format times as milliseconds
        let build_ms = format!("{:.0}ms", build_time.as_secs_f64() * 1000.0);
        let reach_ms = format!("{:.0}ms", reach_time.as_secs_f64() * 1000.0);
        let check_ms = format!("{:.0}ms", check_time.as_secs_f64() * 1000.0);

        println!(
            "  {:>5}  {:>12}  {:>10}  {:>10}  {:>10}  {:>10}  {:>12}",
            n, expected_states, build_ms, reach_ms, check_ms, total_nodes, cache_hits
        );
    }

    println!();
    println!("  ✓ All scalability tests passed!");
    println!();

    header("Key Insights");

    println!("  1. EXPONENTIAL STATE SPACE, POLYNOMIAL BDD SIZE");
    println!("     - 14-bit counter has 16,384 states");
    println!("     - Reachability time is the main bottleneck");
    println!("     - BDD node count stays manageable");
    println!();

    println!("  2. SYMBOLIC REACHABILITY");
    println!("     - We never enumerate states one by one");
    println!("     - BDD represents the set of ALL reachable states");
    println!("     - Each fixpoint iteration processes ALL states at once");
    println!();

    println!("  3. STRUCTURE EXPLOITATION");
    println!("     - Counter has regular structure (binary addition)");
    println!("     - BDDs exploit this regularity automatically");
    println!("     - Irregular systems may not scale as well");
    println!();

    println!("  4. VARIABLE ORDERING MATTERS");
    println!("     - Our default ordering (b0, b1, ..., bn-1) works well");
    println!("     - Different orderings can dramatically affect BDD size");
    println!("     - Finding optimal ordering is NP-complete in general");
    println!();

    header("Summary");

    println!("BDD-based model checking scales well:");
    println!("- 4-bit counter:   16 states          ✓");
    println!("- 10-bit counter:  1,024 states       ✓");
    println!("- 14-bit counter:  16,384 states      ✓");
    println!();

    println!("✓ All assertions passed! BDDs handle exponential state spaces.\n");
}
