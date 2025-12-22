//! # Mutual Exclusion: From Broken to Correct
//!
//! This example demonstrates BDD-based symbolic model checking by comparing
//! **three mutex implementations**: from naive (broken) to correct (Peterson).
//!
//! ## Why Model Checking Matters
//!
//! Concurrency bugs are notoriously hard to find by testing:
//! - Race conditions depend on specific timing/interleaving
//! - Bugs may occur once in millions of runs
//! - Testing gives confidence, but not guarantees
//!
//! Model checking explores **all possible interleavings** exhaustively,
//! proving properties hold or finding counterexamples.
//!
//! ## The Three Implementations
//!
//! 1. **Naive Mutex** (broken): Both processes check and enter without coordination
//!    → Violates mutual exclusion
//!
//! 2. **Flag-based Mutex** (broken): Uses intent flags but no tie-breaker
//!    → Leads to deadlock
//!
//! 3. **Peterson's Algorithm** (correct): Uses flags + turn variable
//!    → Guarantees mutual exclusion and deadlock-freedom
//!
//! ## What We Verify
//!
//! - **Safety (Mutual Exclusion)**: Never two processes in critical section
//! - **Liveness (Deadlock-Freedom)**: Can always eventually enter critical section
//! - **Reachability**: Critical section is actually reachable
//!
//! Run with: `cargo run --example mutex --release`

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use model_checking::*;

fn header(s: &str) {
    println!("{}", s);
    println!("{}", "─".repeat(s.len()));
    println!();
}

fn main() {
    println!("════════════════════════════════════════════");
    println!("  Mutual Exclusion: From Broken to Correct  ");
    println!("════════════════════════════════════════════");
    println!();

    // Run all three implementations and compare results
    println!("This example compares three mutex implementations:\n");
    println!("  1. Naive Mutex     - No synchronization (BROKEN)");
    println!("  2. Flag-based      - Intent flags only (BROKEN - deadlock)");
    println!("  3. Peterson's      - Flags + turn (CORRECT)");
    println!();

    // --- Implementation 1: Naive (broken) ---
    header("IMPLEMENTATION 1: Naive Mutex (No Synchronization)");

    println!("Pseudocode:");
    println!("  Process 0              │  Process 1");
    println!("  ───────────────────────┼─────────────────────────");
    println!("  // No check, just go!  │  // No check, just go!");
    println!("  enter_critical()       │  enter_critical()");
    println!("  // critical section    │  // critical section");
    println!("  exit_critical()        │  exit_critical()\n");

    let naive_results = check_naive_mutex();
    print_results("Naive Mutex", &naive_results);

    // --- Implementation 2: Flag-based (deadlock) ---
    header("IMPLEMENTATION 2: Flag-Based Mutex (Intent Flags Only)");

    println!("Pseudocode:");
    println!("  Process 0              │  Process 1");
    println!("  ───────────────────────┼─────────────────────────");
    println!("  flag[0] = true         │  flag[1] = true");
    println!("  while (flag[1])        │  while (flag[0])");
    println!("    wait()               │    wait()");
    println!("  // critical section    │  // critical section");
    println!("  flag[0] = false        │  flag[1] = false\n");

    println!("Problem: If both set flags simultaneously, both wait forever!\n");

    let flag_results = check_flag_mutex();
    print_results("Flag-Based Mutex", &flag_results);

    // --- Implementation 3: Peterson's Algorithm (correct) ---
    header("IMPLEMENTATION 3: Peterson's Algorithm (Correct)");

    println!("Pseudocode:");
    println!("  Process 0                      │  Process 1");
    println!("  ───────────────────────────────┼────────────────────────────────");
    println!("  flag[0] = true                 │  flag[1] = true");
    println!("  turn = 1  // yield to other    │  turn = 0  // yield to other");
    println!("  while (flag[1] && turn == 1)   │  while (flag[0] && turn == 0)");
    println!("    wait()                       │    wait()");
    println!("  // critical section            │  // critical section");
    println!("  flag[0] = false                │  flag[1] = false\n");

    println!("Key insight: 'turn' breaks symmetry - whoever writes last yields!\n");

    let peterson_results = check_peterson_mutex();
    print_results("Peterson's Algorithm", &peterson_results);

    // --- Summary comparison ---
    header("SUMMARY");
    println!(" Property             │ Naive │ Flags │ Peterson");
    println!("──────────────────────┼───────┼───────┼──────────");
    println!(
        " Mutual Exclusion     │   {}   │   {}   │    {}",
        status_icon(naive_results.mutex),
        status_icon(flag_results.mutex),
        status_icon(peterson_results.mutex)
    );
    println!(
        " Deadlock-Free        │   {}   │   {}   │    {}",
        status_icon(naive_results.deadlock_free),
        status_icon(flag_results.deadlock_free),
        status_icon(peterson_results.deadlock_free)
    );
    println!(
        " P0 Can Enter         │   {}   │   {}   │    {}",
        status_icon(naive_results.p0_reachable),
        status_icon(flag_results.p0_reachable),
        status_icon(peterson_results.p0_reachable)
    );
    println!(
        " P1 Can Enter         │   {}   │   {}   │    {}",
        status_icon(naive_results.p1_reachable),
        status_icon(flag_results.p1_reachable),
        status_icon(peterson_results.p1_reachable)
    );
    println!("\nLegend: ✓ = property holds, ✗ = property violated\n");

    println!("Conclusion:");
    println!("  - Naive mutex has NO synchronization → immediate mutual exclusion violation");
    println!("  - Flag-based adds intent signaling but can deadlock (both wait forever)");
    println!("  - Peterson's algorithm uses a 'turn' variable to break symmetry");
    println!("  - The turn acts as a tie-breaker: whoever sets it last defers to the other\n");

    println!("BDD model checking explored ALL possible interleavings exhaustively,");
    println!("guaranteeing correctness (or finding counterexamples) in milliseconds.");
}

// ============================================================================
// RESULT STRUCTURE
// ============================================================================

/// Results from checking a mutex implementation
struct MutexResults {
    mutex: bool,
    deadlock_free: bool,
    p0_reachable: bool,
    p1_reachable: bool,
    counterexample: Option<Counterexample>,
}

fn status_icon(holds: bool) -> &'static str {
    if holds {
        "✓"
    } else {
        "✗"
    }
}

fn print_results(name: &str, results: &MutexResults) {
    println!("Results for {}:", name);
    println!(
        "  • Mutual Exclusion (AG mutex):       {}",
        if results.mutex { "✓ HOLDS" } else { "✗ VIOLATED" }
    );
    println!(
        "  • Deadlock-Free (AG EF critical):    {}",
        if results.deadlock_free { "✓ HOLDS" } else { "✗ VIOLATED" }
    );
    println!(
        "  • P0 Reachable (EF critical0):       {}",
        if results.p0_reachable { "✓ HOLDS" } else { "✗ VIOLATED" }
    );
    println!(
        "  • P1 Reachable (EF critical1):       {}",
        if results.p1_reachable { "✓ HOLDS" } else { "✗ VIOLATED" }
    );

    // Show counterexample if mutual exclusion is violated
    if !results.mutex {
        if let Some(ref cex) = results.counterexample {
            println!();
            println!("  *** COUNTEREXAMPLE: Mutual Exclusion Violation ***");
            println!();

            // Add annotations and visualize
            let cex = cex.clone().with_annotations();
            let viz = cex
                .visualize()
                .with_label("critical0", |s| s.get("pc0").unwrap_or(false))
                .with_label("critical1", |s| s.get("pc1").unwrap_or(false))
                .with_label("MUTEX", |s| {
                    let c0 = s.get("pc0").unwrap_or(false);
                    let c1 = s.get("pc1").unwrap_or(false);
                    !(c0 && c1) // mutex = not both in critical
                });

            // Indent the visualization
            for line in viz.render().lines() {
                println!("  {}", line);
            }

            // Explain what happened
            println!();
            println!("  Explanation:");
            println!("    The trace shows both processes entering their critical sections");
            println!("    simultaneously (pc0=1 AND pc1=1), violating mutual exclusion.");
            println!();
            println!("    This happens because there's no synchronization mechanism to");
            println!("    prevent concurrent access to the shared resource.");
        }
    }

    // Show deadlock situation
    if !results.deadlock_free && results.mutex {
        println!();
        println!("  *** DEADLOCK DETECTED ***");
        println!();

        println!("  Explanation:");
        println!("    Both processes can get stuck waiting for each other forever.");
        println!("    This happens when both set their flags simultaneously:");
        println!("      • P0 sees flag1=true, waits");
        println!("      • P1 sees flag0=true, waits");
        println!("      • Neither can proceed → DEADLOCK");
        println!();
        println!("    Peterson's algorithm solves this with a 'turn' variable that");
        println!("    breaks the symmetry: whoever writes 'turn' last will yield.");
    }

    println!();
}

// ============================================================================
// IMPLEMENTATION 1: NAIVE MUTEX (BROKEN)
// ============================================================================

/// Naive mutex with no synchronization.
///
/// Both processes can non-deterministically enter/exit critical section
/// without checking what the other is doing. This immediately violates
/// mutual exclusion.
fn check_naive_mutex() -> MutexResults {
    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    // State variables: just the program counters
    // pc0, pc1 ∈ {0, 1} where 1 = in critical section
    let pc0 = Var::new("pc0");
    let pc1 = Var::new("pc1");

    ts.declare_var(pc0.clone());
    ts.declare_var(pc1.clone());

    let pc0_p = ts.var_manager().get_present(&pc0).unwrap();
    let pc1_p = ts.var_manager().get_present(&pc1).unwrap();
    let pc0_n = ts.var_manager().get_next(&pc0).unwrap();
    let pc1_n = ts.var_manager().get_next(&pc1).unwrap();

    let pc0_bdd = bdd.mk_var(pc0_p);
    let pc1_bdd = bdd.mk_var(pc1_p);
    let _pc0_next = bdd.mk_var(pc0_n);
    let _pc1_next = bdd.mk_var(pc1_n);

    // Initial: both outside critical section (pc0=0, pc1=0)
    let initial = bdd.apply_and(bdd.apply_not(pc0_bdd), bdd.apply_not(pc1_bdd));
    ts.set_initial(initial);

    // Transition: either process can freely enter or exit
    // P0: can toggle pc0 non-deterministically
    // P1: can toggle pc1 non-deterministically
    //
    // We model this as: pc0' can be anything, pc1' can be anything
    // (completely unrestricted transitions)
    let transition = bdd.one(); // Any transition is allowed!
    ts.set_transition(transition);

    // Labels
    ts.add_label("critical0".to_string(), pc0_bdd);
    ts.add_label("critical1".to_string(), pc1_bdd);
    let mutex = bdd.apply_not(bdd.apply_and(pc0_bdd, pc1_bdd)); // ¬(pc0 ∧ pc1)
    ts.add_label("mutex".to_string(), mutex);

    // "can progress" = can enter critical section = EF(critical0 ∨ critical1)
    let critical = bdd.apply_or(pc0_bdd, pc1_bdd);
    ts.add_label("critical".to_string(), critical);

    let ts = Rc::new(ts);
    let checker = CtlChecker::new(ts.clone());

    // Check properties
    let mutex_holds = checker.holds_initially(&CtlFormula::atom("mutex").ag());

    // Generate counterexample for mutex violation
    let counterexample = if !mutex_holds {
        let gen = CounterexampleGenerator::new(ts.clone());
        let bad_states = bdd.apply_and(pc0_bdd, pc1_bdd); // Both in critical
        gen.generate_linear(bad_states)
    } else {
        None
    };

    // Deadlock-free: AG EF critical (from any state, can reach critical)
    let deadlock_free = checker.holds_initially(&CtlFormula::atom("critical").ef().ag());

    // Reachability
    let p0_reachable = checker.holds_initially(&CtlFormula::atom("critical0").ef());
    let p1_reachable = checker.holds_initially(&CtlFormula::atom("critical1").ef());

    MutexResults {
        mutex: mutex_holds,
        deadlock_free,
        p0_reachable,
        p1_reachable,
        counterexample,
    }
}

// ============================================================================
// IMPLEMENTATION 2: FLAG-BASED MUTEX (DEADLOCK)
// ============================================================================

/// Flag-based mutex without turn variable.
///
/// Each process sets a flag indicating intent to enter, then waits while
/// the other's flag is set. This ensures mutual exclusion but can deadlock
/// when both set their flags simultaneously.
fn check_flag_mutex() -> MutexResults {
    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    // State variables:
    // - flag0, flag1: intent flags
    // - pc0, pc1: 0=idle, 1=critical
    let flag0 = Var::new("flag0");
    let flag1 = Var::new("flag1");
    let pc0 = Var::new("pc0"); // 0=idle/wanting, 1=critical
    let pc1 = Var::new("pc1");

    ts.declare_var(flag0.clone());
    ts.declare_var(flag1.clone());
    ts.declare_var(pc0.clone());
    ts.declare_var(pc1.clone());

    let flag0_p = ts.var_manager().get_present(&flag0).unwrap();
    let flag1_p = ts.var_manager().get_present(&flag1).unwrap();
    let pc0_p = ts.var_manager().get_present(&pc0).unwrap();
    let pc1_p = ts.var_manager().get_present(&pc1).unwrap();

    let flag0_n = ts.var_manager().get_next(&flag0).unwrap();
    let flag1_n = ts.var_manager().get_next(&flag1).unwrap();
    let pc0_n = ts.var_manager().get_next(&pc0).unwrap();
    let pc1_n = ts.var_manager().get_next(&pc1).unwrap();

    let flag0_bdd = bdd.mk_var(flag0_p);
    let flag1_bdd = bdd.mk_var(flag1_p);
    let pc0_bdd = bdd.mk_var(pc0_p);
    let pc1_bdd = bdd.mk_var(pc1_p);

    let flag0_next = bdd.mk_var(flag0_n);
    let flag1_next = bdd.mk_var(flag1_n);
    let pc0_next = bdd.mk_var(pc0_n);
    let pc1_next = bdd.mk_var(pc1_n);

    // Initial: no flags, not in critical
    let initial = bdd.apply_and_many([
        bdd.apply_not(flag0_bdd),
        bdd.apply_not(flag1_bdd),
        bdd.apply_not(pc0_bdd),
        bdd.apply_not(pc1_bdd),
    ]);
    ts.set_initial(initial);

    // Transitions for P0:
    // 1. Set flag: ¬flag0 → flag0'=1, pc0 unchanged
    // 2. Enter critical: flag0 ∧ ¬flag1 ∧ ¬pc0 → pc0'=1
    // 3. Exit critical: pc0 → pc0'=0, flag0'=0

    // For simplicity, model as interleaved transitions
    let not_flag0 = bdd.apply_not(flag0_bdd);
    let not_flag1 = bdd.apply_not(flag1_bdd);
    let not_pc0 = bdd.apply_not(pc0_bdd);
    let not_pc1 = bdd.apply_not(pc1_bdd);

    // P0 transitions:
    // T1: Idle → set flag: ¬flag0 ∧ ¬pc0 → flag0'=1, keep others
    let p0_set_flag = bdd.apply_and_many([
        not_flag0,
        not_pc0,
        flag0_next,                          // flag0' = 1
        bdd.apply_eq(flag1_next, flag1_bdd), // flag1 unchanged
        bdd.apply_eq(pc0_next, pc0_bdd),     // pc0 unchanged
        bdd.apply_eq(pc1_next, pc1_bdd),     // pc1 unchanged
    ]);

    // T2: Enter critical: flag0 ∧ ¬flag1 ∧ ¬pc0 → pc0'=1
    let p0_enter = bdd.apply_and_many([
        flag0_bdd,
        not_flag1, // Other not wanting (this is the bug condition)
        not_pc0,
        bdd.apply_eq(flag0_next, flag0_bdd),
        bdd.apply_eq(flag1_next, flag1_bdd),
        pc0_next, // pc0' = 1
        bdd.apply_eq(pc1_next, pc1_bdd),
    ]);

    // T3: Exit critical: pc0 → pc0'=0, flag0'=0
    let p0_exit = bdd.apply_and_many([
        pc0_bdd,
        bdd.apply_not(flag0_next), // flag0' = 0
        bdd.apply_eq(flag1_next, flag1_bdd),
        bdd.apply_not(pc0_next), // pc0' = 0
        bdd.apply_eq(pc1_next, pc1_bdd),
    ]);

    // P1 transitions (symmetric):
    let p1_set_flag = bdd.apply_and_many([
        not_flag1,
        not_pc1,
        bdd.apply_eq(flag0_next, flag0_bdd),
        flag1_next,
        bdd.apply_eq(pc0_next, pc0_bdd),
        bdd.apply_eq(pc1_next, pc1_bdd),
    ]);

    let p1_enter = bdd.apply_and_many([
        flag1_bdd,
        not_flag0, // Other not wanting
        not_pc1,
        bdd.apply_eq(flag0_next, flag0_bdd),
        bdd.apply_eq(flag1_next, flag1_bdd),
        bdd.apply_eq(pc0_next, pc0_bdd),
        pc1_next,
    ]);

    let p1_exit = bdd.apply_and_many([
        pc1_bdd,
        bdd.apply_eq(flag0_next, flag0_bdd),
        bdd.apply_not(flag1_next),
        bdd.apply_eq(pc0_next, pc0_bdd),
        bdd.apply_not(pc1_next),
    ]);

    // Combined transition: any of the above
    let transition = bdd.apply_or_many([p0_set_flag, p0_enter, p0_exit, p1_set_flag, p1_enter, p1_exit]);
    ts.set_transition(transition);

    // Labels
    ts.add_label("critical0".to_string(), pc0_bdd);
    ts.add_label("critical1".to_string(), pc1_bdd);
    let mutex = bdd.apply_not(bdd.apply_and(pc0_bdd, pc1_bdd));
    ts.add_label("mutex".to_string(), mutex);
    let critical = bdd.apply_or(pc0_bdd, pc1_bdd);
    ts.add_label("critical".to_string(), critical);

    let ts = Rc::new(ts);
    let checker = CtlChecker::new(ts.clone());

    // Check properties
    let mutex_holds = checker.holds_initially(&CtlFormula::atom("mutex").ag());

    let counterexample = if !mutex_holds {
        let gen = CounterexampleGenerator::new(ts.clone());
        let bad_states = bdd.apply_and(pc0_bdd, pc1_bdd);
        gen.generate_linear(bad_states)
    } else {
        None
    };

    // Deadlock-free: AG EF critical
    let deadlock_free = checker.holds_initially(&CtlFormula::atom("critical").ef().ag());

    // Reachability
    let p0_reachable = checker.holds_initially(&CtlFormula::atom("critical0").ef());
    let p1_reachable = checker.holds_initially(&CtlFormula::atom("critical1").ef());

    MutexResults {
        mutex: mutex_holds,
        deadlock_free,
        p0_reachable,
        p1_reachable,
        counterexample,
    }
}

// ============================================================================
// IMPLEMENTATION 3: PETERSON'S ALGORITHM (CORRECT)
// ============================================================================

/// Peterson's mutual exclusion algorithm.
///
/// Uses two flags (intent to enter) plus a turn variable (tie-breaker).
/// The key insight: when both processes want to enter, the turn variable
/// determines who waits. Whoever wrote to turn last will yield.
///
/// This guarantees both:
/// - Mutual exclusion: at most one in critical section
/// - Deadlock-freedom: if one wants to enter, someone eventually does
fn check_peterson_mutex() -> MutexResults {
    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd.clone());

    // State variables
    let flag0 = Var::new("flag0"); // P0's intent
    let flag1 = Var::new("flag1"); // P1's intent
    let turn = Var::new("turn"); // Whose turn (0 or 1)
    let pc0 = Var::new("pc0"); // P0 in critical section
    let pc1 = Var::new("pc1"); // P1 in critical section

    ts.declare_var(flag0.clone());
    ts.declare_var(flag1.clone());
    ts.declare_var(turn.clone());
    ts.declare_var(pc0.clone());
    ts.declare_var(pc1.clone());

    let flag0_p = ts.var_manager().get_present(&flag0).unwrap();
    let flag1_p = ts.var_manager().get_present(&flag1).unwrap();
    let turn_p = ts.var_manager().get_present(&turn).unwrap();
    let pc0_p = ts.var_manager().get_present(&pc0).unwrap();
    let pc1_p = ts.var_manager().get_present(&pc1).unwrap();

    let flag0_n = ts.var_manager().get_next(&flag0).unwrap();
    let flag1_n = ts.var_manager().get_next(&flag1).unwrap();
    let turn_n = ts.var_manager().get_next(&turn).unwrap();
    let pc0_n = ts.var_manager().get_next(&pc0).unwrap();
    let pc1_n = ts.var_manager().get_next(&pc1).unwrap();

    let flag0_bdd = bdd.mk_var(flag0_p);
    let flag1_bdd = bdd.mk_var(flag1_p);
    let turn_bdd = bdd.mk_var(turn_p);
    let pc0_bdd = bdd.mk_var(pc0_p);
    let pc1_bdd = bdd.mk_var(pc1_p);

    let flag0_next = bdd.mk_var(flag0_n);
    let flag1_next = bdd.mk_var(flag1_n);
    let turn_next = bdd.mk_var(turn_n);
    let pc0_next = bdd.mk_var(pc0_n);
    let pc1_next = bdd.mk_var(pc1_n);

    // Helper: keep all other variables unchanged
    let keep_others = |changed: &[Ref]| -> Vec<Ref> {
        let all_pairs = [
            (flag0_next, flag0_bdd),
            (flag1_next, flag1_bdd),
            (turn_next, turn_bdd),
            (pc0_next, pc0_bdd),
            (pc1_next, pc1_bdd),
        ];
        all_pairs
            .iter()
            .filter(|(next, _)| !changed.contains(next))
            .map(|(next, curr)| bdd.apply_eq(*next, *curr))
            .collect()
    };

    let not_flag0 = bdd.apply_not(flag0_bdd);
    let not_flag1 = bdd.apply_not(flag1_bdd);
    let not_pc0 = bdd.apply_not(pc0_bdd);
    let not_pc1 = bdd.apply_not(pc1_bdd);
    let not_turn = bdd.apply_not(turn_bdd); // turn=0

    // Initial: no flags, not in critical, turn can be anything
    let initial = bdd.apply_and_many([not_flag0, not_flag1, not_pc0, not_pc1]);
    ts.set_initial(initial);

    // P0 transitions:

    // T1: Want to enter: ¬flag0 ∧ ¬pc0 → flag0'=1, turn'=1 (yield to other)
    let p0_want = {
        let guard = bdd.apply_and(not_flag0, not_pc0);
        let effects = vec![
            flag0_next, // flag0' = 1
            turn_next,  // turn' = 1 (yield to P1)
        ];
        let unchanged = keep_others(&effects);
        let mut all: Vec<Ref> = vec![guard];
        all.extend(effects);
        all.extend(unchanged);
        bdd.apply_and_many(all)
    };

    // T2: Enter critical: flag0 ∧ (¬flag1 ∨ turn=0) ∧ ¬pc0 → pc0'=1
    // Peterson's entry condition: either other doesn't want, or it's my turn
    let can_enter_0 = bdd.apply_and(flag0_bdd, bdd.apply_or(not_flag1, not_turn));
    let p0_enter = {
        let guard = bdd.apply_and(can_enter_0, not_pc0);
        let effects = vec![pc0_next]; // pc0' = 1
        let unchanged = keep_others(&effects);
        let mut all: Vec<Ref> = vec![guard];
        all.extend(effects);
        all.extend(unchanged);
        bdd.apply_and_many(all)
    };

    // T3: Exit critical: pc0 → pc0'=0, flag0'=0
    let p0_exit = {
        let guard = pc0_bdd;
        let effects = vec![
            bdd.apply_not(pc0_next),   // pc0' = 0
            bdd.apply_not(flag0_next), // flag0' = 0
        ];
        let unchanged = keep_others(&[pc0_next, flag0_next]);
        let mut all: Vec<Ref> = vec![guard];
        all.extend(effects);
        all.extend(unchanged);
        bdd.apply_and_many(all)
    };

    // P1 transitions (symmetric, but turn'=0 when wanting):

    // T4: Want to enter: ¬flag1 ∧ ¬pc1 → flag1'=1, turn'=0 (yield to other)
    let p1_want = {
        let guard = bdd.apply_and(not_flag1, not_pc1);
        let effects = vec![
            flag1_next,               // flag1' = 1
            bdd.apply_not(turn_next), // turn' = 0 (yield to P0)
        ];
        let unchanged = keep_others(&[flag1_next, turn_next]);
        let mut all: Vec<Ref> = vec![guard];
        all.extend(effects);
        all.extend(unchanged);
        bdd.apply_and_many(all)
    };

    // T5: Enter critical: flag1 ∧ (¬flag0 ∨ turn=1) ∧ ¬pc1 → pc1'=1
    let can_enter_1 = bdd.apply_and(flag1_bdd, bdd.apply_or(not_flag0, turn_bdd));
    let p1_enter = {
        let guard = bdd.apply_and(can_enter_1, not_pc1);
        let effects = vec![pc1_next];
        let unchanged = keep_others(&effects);
        let mut all: Vec<Ref> = vec![guard];
        all.extend(effects);
        all.extend(unchanged);
        bdd.apply_and_many(all)
    };

    // T6: Exit critical: pc1 → pc1'=0, flag1'=0
    let p1_exit = {
        let guard = pc1_bdd;
        let effects = vec![bdd.apply_not(pc1_next), bdd.apply_not(flag1_next)];
        let unchanged = keep_others(&[pc1_next, flag1_next]);
        let mut all: Vec<Ref> = vec![guard];
        all.extend(effects);
        all.extend(unchanged);
        bdd.apply_and_many(all)
    };

    // Combined transition
    let transition = bdd.apply_or_many([p0_want, p0_enter, p0_exit, p1_want, p1_enter, p1_exit]);
    ts.set_transition(transition);

    // Labels
    ts.add_label("critical0".to_string(), pc0_bdd);
    ts.add_label("critical1".to_string(), pc1_bdd);
    let mutex = bdd.apply_not(bdd.apply_and(pc0_bdd, pc1_bdd));
    ts.add_label("mutex".to_string(), mutex);
    let critical = bdd.apply_or(pc0_bdd, pc1_bdd);
    ts.add_label("critical".to_string(), critical);

    let ts = Rc::new(ts);
    let checker = CtlChecker::new(ts.clone());

    // Check properties
    let mutex_holds = checker.holds_initially(&CtlFormula::atom("mutex").ag());

    let counterexample = if !mutex_holds {
        let gen = CounterexampleGenerator::new(ts.clone());
        let bad_states = bdd.apply_and(pc0_bdd, pc1_bdd);
        gen.generate_linear(bad_states)
    } else {
        None
    };

    // Deadlock-free: AG EF critical
    let deadlock_free = checker.holds_initially(&CtlFormula::atom("critical").ef().ag());

    // Reachability
    let p0_reachable = checker.holds_initially(&CtlFormula::atom("critical0").ef());
    let p1_reachable = checker.holds_initially(&CtlFormula::atom("critical1").ef());

    MutexResults {
        mutex: mutex_holds,
        deadlock_free,
        p0_reachable,
        p1_reachable,
        counterexample,
    }
}
