//! Evolving Mutual Exclusion Protocol
//!
//! This example demonstrates incremental verification of an evolving
//! mutual exclusion protocol. We start with a simple 2-process system
//! and incrementally modify it, re-verifying safety at each step.
//!
//! Run with: cargo run --example evolving_mutex --release

use std::rc::Rc;
use std::time::Instant;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use ananke_bdd::types::Var as BddVar;
use incremental_dd::incremental_ts::IncrementalTransSystem;
use incremental_dd::safety::IncrementalSafetyChecker;
use incremental_dd::traits::IncrementalVerifier;
use incremental_dd::{Delta, SystemDelta};
use model_checking::transition::Var;

/// Process states for a simple mutex protocol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProcessState {
    Idle,     // Not interested in critical section
    Trying,   // Trying to enter critical section
    Critical, // In critical section
}

fn main() {
    env_logger::init();

    println!("=== Evolving Mutual Exclusion Verification ===\n");

    let bdd = Rc::new(Bdd::default());
    let mut ts = IncrementalTransSystem::new(bdd.clone());

    // Create variables for 2 processes (2 bits each for 3 states)
    let (p0_b0, p0_b0_next) = ts.declare_var(Var::new("p0_b0"));
    let (p0_b1, p0_b1_next) = ts.declare_var(Var::new("p0_b1"));
    let (p1_b0, p1_b0_next) = ts.declare_var(Var::new("p1_b0"));
    let (p1_b1, p1_b1_next) = ts.declare_var(Var::new("p1_b1"));

    // Helper to encode process state
    let encode_state = |p_b0: BddVar, p_b1: BddVar, state: ProcessState| -> Ref {
        let (b0_val, b1_val) = match state {
            ProcessState::Idle => (false, false),    // 00
            ProcessState::Trying => (true, false),   // 01
            ProcessState::Critical => (false, true), // 10
        };

        let b0_ref = if b0_val { bdd.mk_var(p_b0) } else { -bdd.mk_var(p_b0) };
        let b1_ref = if b1_val { bdd.mk_var(p_b1) } else { -bdd.mk_var(p_b1) };

        bdd.apply_and_many([b0_ref, b1_ref])
    };

    // Process 0 states
    let p0_idle = encode_state(p0_b0, p0_b1, ProcessState::Idle);
    let p0_trying = encode_state(p0_b0, p0_b1, ProcessState::Trying);
    let p0_critical = encode_state(p0_b0, p0_b1, ProcessState::Critical);

    let p0_idle_next = encode_state(p0_b0_next, p0_b1_next, ProcessState::Idle);
    let p0_trying_next = encode_state(p0_b0_next, p0_b1_next, ProcessState::Trying);
    let p0_critical_next = encode_state(p0_b0_next, p0_b1_next, ProcessState::Critical);

    // Process 1 states
    let p1_idle = encode_state(p1_b0, p1_b1, ProcessState::Idle);
    let p1_trying = encode_state(p1_b0, p1_b1, ProcessState::Trying);
    let p1_critical = encode_state(p1_b0, p1_b1, ProcessState::Critical);

    let p1_idle_next = encode_state(p1_b0_next, p1_b1_next, ProcessState::Idle);
    let p1_trying_next = encode_state(p1_b0_next, p1_b1_next, ProcessState::Trying);
    let p1_critical_next = encode_state(p1_b0_next, p1_b1_next, ProcessState::Critical);

    // Unchanged predicates (process stays in same state)
    let p0_unchanged = bdd.apply_or_many([
        bdd.apply_and(p0_idle, p0_idle_next),
        bdd.apply_and(p0_trying, p0_trying_next),
        bdd.apply_and(p0_critical, p0_critical_next),
    ]);

    let p1_unchanged = bdd.apply_or_many([
        bdd.apply_and(p1_idle, p1_idle_next),
        bdd.apply_and(p1_trying, p1_trying_next),
        bdd.apply_and(p1_critical, p1_critical_next),
    ]);

    // === Phase 1: Initial buggy system (no mutex) ===
    println!("Phase 1: Initial system (BUGGY - no mutual exclusion)\n");

    // Initial state: both idle
    let initial = bdd.apply_and_many([p0_idle, p1_idle]);
    ts.set_initial(initial);

    // Transitions (buggy: can enter critical regardless of other process)
    // P0: idle -> trying -> critical -> idle
    let p0_idle_to_trying = bdd.apply_and_many([p0_idle, p0_trying_next, p1_unchanged]);
    let p0_trying_to_critical = bdd.apply_and_many([p0_trying, p0_critical_next, p1_unchanged]);
    let p0_critical_to_idle = bdd.apply_and_many([p0_critical, p0_idle_next, p1_unchanged]);

    // P1: same transitions
    let p1_idle_to_trying = bdd.apply_and_many([p1_idle, p1_trying_next, p0_unchanged]);
    let p1_trying_to_critical = bdd.apply_and_many([p1_trying, p1_critical_next, p0_unchanged]);
    let p1_critical_to_idle = bdd.apply_and_many([p1_critical, p1_idle_next, p0_unchanged]);

    let trans_buggy = bdd.apply_or_many([
        p0_idle_to_trying,
        p0_trying_to_critical,
        p0_critical_to_idle,
        p1_idle_to_trying,
        p1_trying_to_critical,
        p1_critical_to_idle,
    ]);

    ts.set_transition(trans_buggy);

    // Safety property: not (p0_critical AND p1_critical)
    let mutex_invariant = -bdd.apply_and_many([p0_critical, p1_critical]);

    let mut checker = IncrementalSafetyChecker::new(ts, mutex_invariant);

    let start = Instant::now();
    let result = checker.verify();
    let time1 = start.elapsed();

    println!("  Result: {:?}", result);
    println!("  Time: {:?}", time1);
    println!("  Safe: {}", result.holds());
    assert!(!result.holds(), "Phase 1: Buggy mutex should be unsafe");
    println!("  ✓ Unsafety detected as expected");

    // === Phase 2: Fix the bug - add guard on entering critical section ===
    println!("\nPhase 2: Fix mutex (add guard: can't enter if other is critical)\n");

    // Remove buggy transitions
    let ts = checker.ts_mut();

    // New transitions with guards
    // P0: trying -> critical ONLY IF p1 is NOT critical
    let p0_trying_to_critical_fixed = bdd.apply_and_many([p0_trying, p0_critical_next, p1_unchanged, -p1_critical]);

    // P1: trying -> critical ONLY IF p0 is NOT critical
    let p1_trying_to_critical_fixed = bdd.apply_and_many([p1_trying, p1_critical_next, p0_unchanged, -p0_critical]);

    let trans_fixed = bdd.apply_or_many([
        p0_idle_to_trying,
        p0_trying_to_critical_fixed,
        p0_critical_to_idle,
        p1_idle_to_trying,
        p1_trying_to_critical_fixed,
        p1_critical_to_idle,
    ]);

    ts.set_transition(trans_fixed);

    // Compute the delta (what changed)
    let removed_trans = bdd.apply_or(p0_trying_to_critical, p1_trying_to_critical);
    let added_trans = bdd.apply_or(p0_trying_to_critical_fixed, p1_trying_to_critical_fixed);

    let delta = SystemDelta::transitions(Delta::new().with_added(added_trans).with_removed(removed_trans));

    let start = Instant::now();
    let result = checker.update(delta);
    let time2 = start.elapsed();

    println!("  Update result: {:?}", result);
    println!("  Time: {:?}", time2);
    assert!(result.holds(), "Phase 2: Fixed mutex should be safe");
    println!("  Property holds: {} ✓", result.holds());

    // === Phase 3: Add a "fast path" transition (still safe) ===
    println!("\nPhase 3: Add fast path (idle -> critical if other is idle)\n");

    // Fast path: if other process is idle, can go directly to critical
    let p0_fast = bdd.apply_and_many([p0_idle, p0_critical_next, p1_unchanged, p1_idle]);
    let p1_fast = bdd.apply_and_many([p1_idle, p1_critical_next, p0_unchanged, p0_idle]);

    let fast_trans = bdd.apply_or(p0_fast, p1_fast);

    let delta = SystemDelta::transitions(Delta::addition(fast_trans));

    let start = Instant::now();
    let result = checker.update(delta);
    let time3 = start.elapsed();

    println!("  Update result: {:?}", result);
    println!("  Time: {:?}", time3);
    assert!(result.holds(), "Phase 3: Fast path should remain safe");
    println!("  Property holds: {} ✓", result.holds());

    // === Phase 4: Accidentally add buggy transition again ===
    println!("\nPhase 4: Regression - accidentally add buggy transition\n");

    let buggy_trans = p0_trying_to_critical; // No guard!
    let delta = SystemDelta::transitions(Delta::addition(buggy_trans));

    let start = Instant::now();
    let result = checker.update(delta);
    let time4 = start.elapsed();

    println!("  Update result: {:?}", result);
    println!("  Time: {:?}", time4);
    assert!(!result.holds(), "Phase 4: Regression should break safety");
    println!("  Property holds: {} (regression detected ✓)", result.holds());

    // === Summary ===
    println!("\n=== Summary ===");
    println!("Phase 1 (buggy):      {:?} - unsafe ✓", time1);
    println!("Phase 2 (fixed):      {:?} - safe ✓", time2);
    println!("Phase 3 (fast path):  {:?} - safe ✓", time3);
    println!("Phase 4 (regression): {:?} - unsafe (caught!) ✓", time4);

    let metrics = checker.ts().metrics();
    println!("\nIncremental Metrics:");
    println!("  Local changes: {}", metrics.local_change_count);
    println!("  Global rebuilds: {}", metrics.global_rebuild_count);
    println!("\n✓ All mutex verification tests passed!");
}
