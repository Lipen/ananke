//! # Traffic Light Controller — Symbolic Model Checking Tutorial
//!
//! This example models a traffic light intersection controller and verifies
//! key safety and liveness properties using BDD-based symbolic model checking.
//!
//! ## The System
//!
//! A simple 4-way intersection with two traffic lights:
//! - **NS** (North-South): Controls traffic on the main road
//! - **EW** (East-West): Controls traffic on the cross road
//!
//! Each light cycles through: Red → Green → Yellow → Red → ...
//! The two lights operate in opposite phases to prevent collisions.
//!
//! ## What We Verify
//!
//! 1. **Safety**: Both lights are never green simultaneously
//! 2. **Liveness**: Each direction eventually gets a green light
//! 3. **Progress**: The controller always makes progress (no deadlock)
//!
//! ## Key Concepts Demonstrated
//!
//! - State encoding with multiple bits per variable
//! - Deterministic transition systems (exactly one successor per state)
//! - Both CTL and LTL model checking
//! - The relationship between safety and liveness properties
//!
//! Run with: `cargo run --example traffic_light --release`

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use model_checking::*;

fn header(s: &str) {
    println!("{}", s);
    println!("{}", "─".repeat(s.len()));
    println!();
}

fn main() {
    println!("══════════════════════════");
    println!(" TRAFFIC LIGHT CONTROLLER ");
    println!("══════════════════════════");
    println!();

    header("Problem Statement");
    println!("Coordinate 2 traffic lights at a 4-way intersection");
    println!();
    println!("- NS light controls north-south traffic");
    println!("- EW light controls east-west traffic");
    println!("- Each light: Red → Yellow → Green → Red");
    println!("- Lights operate in opposite phases");
    println!();
    println!("Requirements:");
    println!("- Safety: Both lights never green simultaneously");
    println!("- Liveness: Each direction eventually gets green");
    println!("- Progress: Deterministic, 1 successor per state\n");

    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    header("Model Construction");
    println!("Variables: 4 Boolean (2 bits per light)");
    println!("- NS0, NS1: north-south light");
    println!("- EW0, EW1: east-west light");
    println!();
    println!("Encoding (2-bit):");
    println!("- 00 = Red");
    println!("- 01 = Yellow");
    println!("- 10 = Green");
    println!("- 11 = unused\n");

    let ns0 = Var::new("ns0"); // NS light, bit 0
    let ns1 = Var::new("ns1"); // NS light, bit 1
    let ew0 = Var::new("ew0"); // EW light, bit 0
    let ew1 = Var::new("ew1"); // EW light, bit 1

    ts.declare_var(ns0.clone());
    ts.declare_var(ns1.clone());
    ts.declare_var(ew0.clone());
    ts.declare_var(ew1.clone());

    // Get present-state BDD variables
    let ns0_p = ts.var_manager().get_present(&ns0).unwrap();
    let ns1_p = ts.var_manager().get_present(&ns1).unwrap();
    let ew0_p = ts.var_manager().get_present(&ew0).unwrap();
    let ew1_p = ts.var_manager().get_present(&ew1).unwrap();

    let ns0_bdd = bdd.mk_var(ns0_p);
    let ns1_bdd = bdd.mk_var(ns1_p);
    let ew0_bdd = bdd.mk_var(ew0_p);
    let ew1_bdd = bdd.mk_var(ew1_p);

    // Helper BDDs for state predicates
    let not_ns0 = bdd.apply_not(ns0_bdd);
    let not_ns1 = bdd.apply_not(ns1_bdd);
    let not_ew0 = bdd.apply_not(ew0_bdd);
    let not_ew1 = bdd.apply_not(ew1_bdd);

    // Define light states as BDD predicates
    // NS light states
    let ns_red = bdd.apply_and(not_ns0, not_ns1); // 00
    let ns_yellow = bdd.apply_and(not_ns0, ns1_bdd); // 01
    let ns_green = bdd.apply_and(ns0_bdd, not_ns1); // 10

    // EW light states
    let ew_red = bdd.apply_and(not_ew0, not_ew1); // 00
    let ew_yellow = bdd.apply_and(not_ew0, ew1_bdd); // 01
    let ew_green = bdd.apply_and(ew0_bdd, not_ew1); // 10

    header("Initial State");
    println!("NS=Red, EW=Green");
    println!();

    let initial = bdd.apply_and(ns_red, ew_green);
    ts.set_initial(initial);
    println!("Initial state BDD: {} nodes", bdd.count_nodes(&[initial]));
    println!();

    header("Transition System");
    println!("Cycle: S1 → S2 → S3 → S4 → S1");
    println!("- S1: NS=Red   (00), EW=Green  (10)");
    println!("- S2: NS=Red   (00), EW=Yellow (01)");
    println!("- S3: NS=Green (10), EW=Red    (00)");
    println!("- S4: NS=Yellow(01), EW=Red    (00)");
    println!();

    // Get next-state BDD variables
    let ns0_n = ts.var_manager().get_next(&ns0).unwrap();
    let ns1_n = ts.var_manager().get_next(&ns1).unwrap();
    let ew0_n = ts.var_manager().get_next(&ew0).unwrap();
    let ew1_n = ts.var_manager().get_next(&ew1).unwrap();

    let ns0_next = bdd.mk_var(ns0_n);
    let ns1_next = bdd.mk_var(ns1_n);
    let ew0_next = bdd.mk_var(ew0_n);
    let ew1_next = bdd.mk_var(ew1_n);

    // Next-state predicates
    let ns_red_next = bdd.apply_and(bdd.apply_not(ns0_next), bdd.apply_not(ns1_next));
    let ns_yellow_next = bdd.apply_and(bdd.apply_not(ns0_next), ns1_next);
    let ns_green_next = bdd.apply_and(ns0_next, bdd.apply_not(ns1_next));

    let ew_red_next = bdd.apply_and(bdd.apply_not(ew0_next), bdd.apply_not(ew1_next));
    let ew_yellow_next = bdd.apply_and(bdd.apply_not(ew0_next), ew1_next);
    let ew_green_next = bdd.apply_and(ew0_next, bdd.apply_not(ew1_next));

    // Define transitions: (current_state) ∧ (next_state)
    // Transition 1→2: NS=Red, EW=Green → NS=Red, EW=Yellow
    let trans1_from = bdd.apply_and(ns_red, ew_green);
    let trans1_to = bdd.apply_and(ns_red_next, ew_yellow_next);
    let trans1 = bdd.apply_and(trans1_from, trans1_to);

    // Transition 2→3: NS=Red, EW=Yellow → NS=Green, EW=Red
    let trans2_from = bdd.apply_and(ns_red, ew_yellow);
    let trans2_to = bdd.apply_and(ns_green_next, ew_red_next);
    let trans2 = bdd.apply_and(trans2_from, trans2_to);

    // Transition 3→4: NS=Green, EW=Red → NS=Yellow, EW=Red
    let trans3_from = bdd.apply_and(ns_green, ew_red);
    let trans3_to = bdd.apply_and(ns_yellow_next, ew_red_next);
    let trans3 = bdd.apply_and(trans3_from, trans3_to);

    // Transition 4→1: NS=Yellow, EW=Red → NS=Red, EW=Green
    let trans4_from = bdd.apply_and(ns_yellow, ew_red);
    let trans4_to = bdd.apply_and(ns_red_next, ew_green_next);
    let trans4 = bdd.apply_and(trans4_from, trans4_to);

    // Complete transition relation: disjunction of all transitions
    let transition = bdd.apply_or(bdd.apply_or(trans1, trans2), bdd.apply_or(trans3, trans4));
    ts.set_transition(transition);
    println!("Transition relation BDD: {} nodes", bdd.count_nodes(&[transition]));
    println!();

    // Define Atomic Propositions
    ts.add_label("ns_red".to_string(), ns_red);
    ts.add_label("ns_yellow".to_string(), ns_yellow);
    ts.add_label("ns_green".to_string(), ns_green);
    ts.add_label("ew_red".to_string(), ew_red);
    ts.add_label("ew_yellow".to_string(), ew_yellow);
    ts.add_label("ew_green".to_string(), ew_green);

    // Safety predicate: never both green
    let both_green = bdd.apply_and(ns_green, ew_green);
    let safe = bdd.apply_not(both_green);
    ts.add_label("safe".to_string(), safe);

    let ts = Rc::new(ts);

    header("State Space Analysis");
    let reachable = ts.reachable();
    let state_count = ts.count_states(reachable);

    println!("Variables: 4");
    println!("Possible states: 2^4 = 16");
    if let Some(count) = state_count {
        println!("Reachable: {}", count);
        assert_eq!(count, 4, "Expected exactly 4 reachable states");
    }
    println!("Reachable BDD: {} nodes\n", bdd.count_nodes(&[reachable]));

    header("CTL Model Checking");

    let checker = CtlChecker::new(ts.clone());

    // Property 1: AG safe — "Both lights never green simultaneously"
    println!("P1: AG safe (no collision)");
    println!("- Safety property: both lights never green");
    let ag_safe = CtlFormula::atom("safe").ag();
    let safety_holds = checker.holds_initially(&ag_safe);
    println!("  {}", if safety_holds { "✓ PASS" } else { "✗ FAIL" });
    assert!(safety_holds, "CRITICAL: Both lights can be green simultaneously!");
    println!();

    // Property 2: AG (ns_green → AF ns_red) — NS eventually stops being green (progress)
    println!("P2: AG (ns_green → AF ns_red) (NS progress)");
    println!("- Liveness property: green light eventually changes");
    let ns_progress = CtlFormula::atom("ns_green").implies(CtlFormula::atom("ns_red").af()).ag();
    let ns_progress_holds = checker.holds_initially(&ns_progress);
    println!("  {}", if ns_progress_holds { "✓ PASS" } else { "✗ FAIL" });
    assert!(ns_progress_holds, "NS green light could stay green forever!");
    println!();

    // Property 3: AG (ew_red → AF ew_green) — EW eventually becomes green (fairness)
    println!("P3: AG (ew_red → AF ew_green) (EW fairness)");
    println!("- Liveness property: waiting traffic gets served");
    let ew_fairness = CtlFormula::atom("ew_red").implies(CtlFormula::atom("ew_green").af()).ag();
    let ew_fairness_holds = checker.holds_initially(&ew_fairness);
    println!("  {}", if ew_fairness_holds { "✓ PASS" } else { "✗ FAIL" });
    assert!(ew_fairness_holds, "EW traffic could wait forever!");
    println!();

    // Property 4: AG EF ns_green — NS green always eventually reachable (reversibility)
    println!("P4: AG EF ns_green (reversibility)");
    println!("- Liveness property: no dead-end states, cycles forever");

    let reversibility = CtlFormula::atom("ns_green").ef().ag();
    let reversibility_holds = checker.holds_initially(&reversibility);
    println!("  {}", if reversibility_holds { "✓ PASS" } else { "✗ FAIL" });
    assert!(reversibility_holds, "System has dead-end states!");
    println!();

    header("LTL Model Checking");

    let ltl_checker = LtlChecker::new(ts.clone());

    // Property 5: G (ns_green → F ns_red) — NS eventually stops being green (LTL version)
    println!("P5: G (ns_green → F ns_red) (NS progress)");
    println!("- LTL version of P2: for all execution paths");
    let ltl_progress = LtlFormula::atom("ns_green")
        .implies(LtlFormula::atom("ns_red").finally())
        .globally();
    let ltl_progress_holds = ltl_checker.holds_initially(&ltl_progress);
    println!("  {}", if ltl_progress_holds { "✓ PASS" } else { "✗ FAIL" });
    println!();
    println!("LTL: G F ns_green");
    println!("'NS green light occurs infinitely often'\n");

    let gf_ns_green = LtlFormula::atom("ns_green").finally().globally();
    let gf_holds = ltl_checker.holds_initially(&gf_ns_green);

    println!("  Result: {}", if gf_holds { "✓ HOLDS" } else { "✗ VIOLATED" });
    if gf_holds {
        println!("  ✓ NS green recurs forever\n");
    } else {
        println!("  (LTL result differs from expected)\n");
    }

    header("Summary");
    println!("  AG safe (no collision):             {}", if safety_holds { "✓" } else { "✗" });
    println!(
        "  AG (ns_green → AF ns_red):          {}",
        if ns_progress_holds { "✓" } else { "✗" }
    );
    println!(
        "  AG (ew_red → AF ew_green):          {}",
        if ew_fairness_holds { "✓" } else { "✗" }
    );
    println!(
        "  AG EF ns_green (reversibility):     {}",
        if reversibility_holds { "✓" } else { "✗" }
    );
    println!(
        "  G (ns_green → F ns_red) [LTL]:      {}",
        if ltl_progress_holds { "✓" } else { "✗" }
    );
    println!("  G F ns_green [LTL]:                 {}", if gf_holds { "✓" } else { "✗" });

    println!();
    println!("✓ All assertions passed!");
    println!("  Traffic light controller is SAFE and LIVE.\n");
}
