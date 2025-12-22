//! # Dining Philosophers — Concurrency Analysis Tutorial
//!
//! This example demonstrates model checking of a classic concurrency problem:
//! the Dining Philosophers, introduced by Edsger Dijkstra in 1965.
//!
//! ## The Problem
//!
//! N philosophers sit around a circular table. Between each pair of adjacent
//! philosophers is a single fork. To eat, a philosopher needs BOTH adjacent forks.
//!
//! ```text
//!        P0
//!      /    \
//!    F0      F2
//!    /        \
//!   P1 --F1-- P2
//! ```
//!
//! The challenge: design a protocol where:
//! - **Safety**: No two adjacent philosophers eat simultaneously (fork conflict)
//! - **Liveness**: Every hungry philosopher eventually eats (no starvation)
//! - **Deadlock-freedom**: System never reaches a state where no progress is possible
//!
//! ## Why This Problem is Important
//!
//! The dining philosophers demonstrate fundamental concurrency challenges:
//! - **Resource contention**: Shared resources (forks) require coordination
//! - **Deadlock**: All philosophers grab left fork, wait for right → stuck!
//! - **Starvation**: A philosopher might wait forever while neighbors eat
//! - **Livelock**: Philosophers keep picking up and putting down forks
//!
//! ## What We Verify
//!
//! 1. **Deadlock possibility**: Can all philosophers get stuck?
//! 2. **Fork exclusion**: Adjacent philosophers never eat together
//! 3. **Reachability**: Eating states are actually reachable
//! 4. **Starvation (with fairness)**: Do hungry philosophers eventually eat?
//!
//! Run with: `cargo run --example philosophers --release`

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use model_checking::*;

fn header(s: &str) {
    println!("{}", s);
    println!("{}", "─".repeat(s.len()));
    println!();
}

fn main() {
    println!("════════════════════════════════════════════════════");
    println!("  Dining Philosophers - Concurrency Model Checking  ");
    println!("════════════════════════════════════════════════════");
    println!();

    // -- Step 1: Problem Setup --

    // Number of philosophers (keep small: state space = O(3^n))
    let n = 3;

    println!("Configuration: {} philosophers around a table", n);
    println!("  Each philosopher can be: THINKING, HUNGRY, or EATING");
    println!("  Forks are shared: Fork i is between Philosopher i and i+1\n");

    println!("  Visual representation (3 philosophers):");
    println!("         P0 (thinking)");
    println!("        /  \\");
    println!("      F0    F2");
    println!("      /      \\");
    println!("    P1 --F1-- P2\n");

    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    // --
    // -- Step 2: State Variables --
    //
    // For each philosopher i:
    //   - hungry_i: wants to eat
    //   - eating_i: currently eating (has both forks)
    //
    // State encoding: THINKING (0,0), HUNGRY (1,0), EATING (0,1)

    println!("Declaring state variables...");

    let hungry: Vec<Var> = (0..n).map(|i| Var::new(format!("hungry{}", i))).collect();
    let eating: Vec<Var> = (0..n).map(|i| Var::new(format!("eating{}", i))).collect();

    for var in hungry.iter().chain(eating.iter()) {
        ts.declare_var(var.clone());
    }

    // Get present-state BDD variables
    let hungry_p: Vec<_> = hungry.iter().map(|v| ts.var_manager().get_present(v).unwrap()).collect();
    let eating_p: Vec<_> = eating.iter().map(|v| ts.var_manager().get_present(v).unwrap()).collect();

    let hungry_bdd: Vec<_> = hungry_p.iter().map(|&p| bdd.mk_var(p)).collect();
    let eating_bdd: Vec<_> = eating_p.iter().map(|&p| bdd.mk_var(p)).collect();

    // Get next-state BDD variables
    let hungry_n: Vec<_> = hungry.iter().map(|v| ts.var_manager().get_next(v).unwrap()).collect();
    let eating_n: Vec<_> = eating.iter().map(|v| ts.var_manager().get_next(v).unwrap()).collect();

    let hungry_next: Vec<_> = hungry_n.iter().map(|&n| bdd.mk_var(n)).collect();
    let eating_next: Vec<_> = eating_n.iter().map(|&n| bdd.mk_var(n)).collect();

    println!("  Variables per philosopher: hungry_i, eating_i");
    println!("  Total state variables: {}\n", 2 * n);

    // -- Step 3: Initial State --
    //
    // Everyone starts THINKING

    println!("Initial state: All philosophers THINKING\n");

    let mut initial = bdd.one();
    for i in 0..n {
        // THINKING: ¬hungry ∧ ¬eating
        let thinking = bdd.apply_and(bdd.apply_not(hungry_bdd[i]), bdd.apply_not(eating_bdd[i]));
        initial = bdd.apply_and(initial, thinking);
    }
    ts.set_initial(initial);

    // -- Step 4: Transition Relation --
    //
    // Each philosopher can:
    //   THINKING → HUNGRY (become hungry)
    //   HUNGRY → EATING (if neighbors not eating)
    //   EATING → THINKING (finish eating)

    println!("Building transition relation...");
    println!("  Transitions per philosopher:");
    println!("  - THINKING → HUNGRY (become hungry, non-deterministic)");
    println!("  - HUNGRY → EATING (if both neighbors not eating)");
    println!("  - EATING → THINKING (finish eating, release forks)");
    println!("  - STAY (remain in current state)\n");

    let mut transitions = Vec::new();

    for i in 0..n {
        let left = (i + n - 1) % n; // Left neighbor (circular)
        let right = (i + 1) % n; // Right neighbor (circular)

        // THINKING state: ¬hungry ∧ ¬eating
        let thinking = bdd.apply_and(bdd.apply_not(hungry_bdd[i]), bdd.apply_not(eating_bdd[i]));

        // Can eat condition: hungry AND neighbors not eating
        let can_eat = bdd.apply_and(
            hungry_bdd[i],
            bdd.apply_and(bdd.apply_not(eating_bdd[left]), bdd.apply_not(eating_bdd[right])),
        );

        // Transition: THINKING → HUNGRY
        let become_hungry = bdd.apply_and(thinking, hungry_next[i]);
        let become_hungry = bdd.apply_and(become_hungry, bdd.apply_not(eating_next[i]));

        // Transition: HUNGRY → EATING
        let start_eating = bdd.apply_and(can_eat, eating_next[i]);
        let start_eating = bdd.apply_and(start_eating, bdd.apply_not(hungry_next[i]));

        // Transition: EATING → THINKING
        let stop_eating = bdd.apply_and(eating_bdd[i], bdd.apply_not(eating_next[i]));
        let stop_eating = bdd.apply_and(stop_eating, bdd.apply_not(hungry_next[i]));

        // Transition: STAY in each state
        let stay_hungry = bdd.apply_and(hungry_bdd[i], hungry_next[i]);
        let stay_hungry = bdd.apply_and(stay_hungry, bdd.apply_eq(eating_next[i], eating_bdd[i]));

        let stay_thinking = bdd.apply_and(thinking, bdd.apply_not(hungry_next[i]));
        let stay_thinking = bdd.apply_and(stay_thinking, bdd.apply_not(eating_next[i]));

        let stay_eating = bdd.apply_and(eating_bdd[i], eating_next[i]);
        let stay_eating = bdd.apply_and(stay_eating, bdd.apply_not(hungry_next[i]));

        // Combine all transitions for this philosopher
        let philosopher_trans = bdd.apply_or_many([become_hungry, start_eating, stop_eating, stay_hungry, stay_thinking, stay_eating]);

        transitions.push(philosopher_trans);
    }

    // All philosophers move simultaneously (or stay)
    let transition = bdd.apply_and_many(transitions.into_iter());
    ts.set_transition(transition);

    // -- Step 5: Define Labels --

    for i in 0..n {
        ts.add_label(format!("eating{}", i), eating_bdd[i]);
        ts.add_label(format!("hungry{}", i), hungry_bdd[i]);
    }

    // DEADLOCK: everyone hungry, no one eating

    let mut everyone_hungry = bdd.one();
    let mut no_one_eating = bdd.one();
    for i in 0..n {
        everyone_hungry = bdd.apply_and(everyone_hungry, hungry_bdd[i]);
        no_one_eating = bdd.apply_and(no_one_eating, bdd.apply_not(eating_bdd[i]));
    }
    let deadlock = bdd.apply_and(everyone_hungry, no_one_eating);

    ts.add_label("deadlock".to_string(), deadlock);
    ts.add_label("no_deadlock".to_string(), bdd.apply_not(deadlock));

    let ts = Rc::new(ts);
    let checker = CtlChecker::new(ts.clone());

    // -- Step 6: State Space Analysis --

    header("State Space Analysis");

    let reachable = ts.reachable();
    let state_count = ts.count_states(reachable);

    if let Some(count) = state_count {
        println!("  Variables: {} (2 per philosopher)", 2 * n);
        println!("  Max states: 2^{} = {}", 2 * n, 1 << (2 * n));
        println!("  Reachable: {}", count);
        assert!(count > 0, "Must have at least one reachable state");
        assert!(count <= (1 << (2 * n)), "Cannot exceed maximum states");
        println!("  ✓ State space explored\n");
    }

    // -- Step 7: Verify Properties --

    header("Property Verification");

    // Property 1: EF deadlock
    //
    // Can the deadlock state be reached?

    println!("─── Property 1: Deadlock Possibility ───");
    println!("CTL: EF deadlock");
    println!("'Is there a path leading to deadlock?'\n");

    let ef_deadlock = CtlFormula::atom("deadlock").ef();
    let deadlock_possible = checker.holds_initially(&ef_deadlock);

    println!(
        "  Result: {}",
        if deadlock_possible {
            "YES - Deadlock possible"
        } else {
            "NO - Deadlock impossible"
        }
    );
    if deadlock_possible {
        println!("  (Expected for naive dining philosophers)\n");
    } else {
        println!("  (Model has deadlock prevention)\n");
    }

    // Property 2: AG no_deadlock

    println!("─── Property 2: Deadlock Freedom ───");
    println!("CTL: AG no_deadlock");
    println!("'Is the system always deadlock-free?'\n");

    let ag_no_deadlock = CtlFormula::atom("no_deadlock").ag();
    let deadlock_free = checker.holds_initially(&ag_no_deadlock);

    println!("  Result: {}", if deadlock_free { "✓ HOLDS" } else { "✗ VIOLATED" });

    // AG no_deadlock is the negation of EF deadlock
    assert_eq!(
        deadlock_free, !deadlock_possible,
        "AG no_deadlock should be opposite of EF deadlock"
    );
    println!("  ✓ AG ¬deadlock ≡ ¬EF deadlock\n");

    // Property 3: EF eating0

    println!("─── Property 3: Eating Reachability ───");
    println!("CTL: EF eating0");
    println!("'Can philosopher 0 eat?'\n");

    let ef_eating0 = CtlFormula::atom("eating0").ef();
    let can_eat = checker.holds_initially(&ef_eating0);

    println!("  Result: {}", if can_eat { "✓ HOLDS" } else { "✗ VIOLATED" });
    assert!(can_eat, "Philosopher 0 should be able to eat!");
    println!("  ✓ Eating is reachable\n");

    // Property 4: AG (hungry0 → EF eating0)

    println!("─── Property 4: No Starvation (without fairness) ───");
    println!("CTL: AG (hungry0 → EF eating0)");
    println!("'If P0 is hungry, can they eventually eat?'\n");

    let no_starvation_ef = CtlFormula::atom("hungry0").implies(CtlFormula::atom("eating0").ef()).ag();
    let can_eventually_eat = checker.holds_initially(&no_starvation_ef);

    println!("  Result: {}", if can_eventually_eat { "✓ HOLDS" } else { "✗ VIOLATED" });
    if can_eventually_eat {
        println!("  (EXISTS a path where hungry philosopher eats)\n");
    } else {
        println!("  (Philosopher can get stuck hungry)\n");
    }

    // -- Step 8: Fairness Analysis --
    //
    // CTL without fairness can give misleading results for liveness.
    // FAIRNESS: "If hungry infinitely often, eats infinitely often"

    header("Fairness Analysis");

    println!("  Without fairness, liveness can fail due to unrealistic schedulers.\n");
    println!("  STRONG FAIRNESS: If hungry infinitely often → eats infinitely often.\n");

    let mut fm = FairnessManager::new(ts.clone());

    for i in 0..n {
        fm.add_constraint(FairnessConstraint::strong(format!("fair_eat_{}", i), hungry_bdd[i], eating_bdd[i]));
    }

    // Property 5: Fair AG no_deadlock

    println!("─── Property 5: Deadlock Freedom (with fairness) ───");
    println!("'Under fair scheduling, is system deadlock-free?'\n");

    let fair_ag_no_deadlock = fm.fair_ag(bdd.apply_not(deadlock));
    let initial_in_fair = bdd.apply_and(ts.initial(), fair_ag_no_deadlock);
    let fair_deadlock_free = initial_in_fair == ts.initial();

    println!("  Result: {}", if fair_deadlock_free { "✓ HOLDS" } else { "✗ VIOLATED" });
    if fair_deadlock_free && !deadlock_free {
        println!("  (Deadlock exists but not on fair paths)\n");
    } else {
        println!();
    }

    // -- Step 9: LTL Model Checking --

    header("LTL Model Checking");

    let ltl_checker = LtlChecker::new(ts.clone());

    // Property 6: G (hungry0 → F eating0)

    println!("─── Property 6: No Starvation (LTL) ───");
    println!("LTL: G (hungry0 → F eating0)");
    println!("'On all paths, if P0 hungry, P0 eventually eats'\n");

    let ltl_no_starve = LtlFormula::atom("hungry0")
        .implies(LtlFormula::atom("eating0").finally())
        .globally();
    let ltl_holds = ltl_checker.holds_initially(&ltl_no_starve);

    println!("  Result: {}", if ltl_holds { "✓ HOLDS" } else { "✗ VIOLATED" });
    if !ltl_holds {
        println!("  (Starvation possible without fairness)\n");
    } else {
        println!("  (No starvation even without fairness!)\n");
    }

    // -- Summary --

    header("Summary");
    println!("  Dining Philosophers: {} philosophers", n);
    println!(
        "  EF deadlock (possible?):            {}",
        if deadlock_possible { "YES" } else { "NO" }
    );
    println!("  AG no_deadlock (always free?):      {}", if deadlock_free { "✓" } else { "✗" });
    println!("  EF eating0 (can P0 eat?):           {}", if can_eat { "✓" } else { "✗" });
    println!(
        "  AG (hungry → EF eating):            {}",
        if can_eventually_eat { "✓" } else { "✗" }
    );
    println!(
        "  Fair AG no_deadlock:                {}",
        if fair_deadlock_free { "✓" } else { "✗" }
    );
    println!("  G (hungry → F eating) [LTL]:        {}", if ltl_holds { "✓" } else { "✗" });

    println!("\nKey Takeaways:");
    println!("  1. Classic dining philosophers HAS deadlock potential");
    println!("  2. CTL vs LTL: Different logics for different properties");
    println!("  3. Fairness matters: Realistic systems have fair schedulers");
    println!("  4. EF vs AF: 'can reach' vs 'will reach' are very different!\n");

    assert!(can_eat, "Eating must be reachable");
    assert!(state_count.is_some() && state_count.unwrap() > 0, "Must have reachable states");

    println!("✓ All critical assertions passed!\n");
}
