//! Simple incremental reachability demonstration.
//!
//! This example shows how to use the incremental transition system
//! to efficiently update reachability when transitions are added.
//!
//! Run with: cargo run --example simple_reachability --release

use std::rc::Rc;
use std::time::Instant;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use incremental_dd::incremental_ts::IncrementalTransSystem;
use model_checking::transition::Var;

fn main() {
    env_logger::init();

    println!("=== Incremental Reachability Demo ===\n");

    let bdd = Rc::new(Bdd::default());
    let mut ts = IncrementalTransSystem::new(bdd.clone());

    // Create a chain of states: s0 -> s1 -> s2 -> s3 -> s4
    // We'll build this incrementally

    // Declare variables for 3-bit state encoding (8 states possible)
    let (b0, b0_next) = ts.declare_var(Var::new("b0"));
    let (b1, b1_next) = ts.declare_var(Var::new("b1"));
    let (b2, b2_next) = ts.declare_var(Var::new("b2"));

    // Helper to create state encoding
    let state = |n: u8| -> Ref {
        let b0_val = (n & 1) != 0;
        let b1_val = (n & 2) != 0;
        let b2_val = (n & 4) != 0;

        let mut s = bdd.one();
        s = bdd.apply_and(s, if b0_val { bdd.mk_var(b0) } else { -bdd.mk_var(b0) });
        s = bdd.apply_and(s, if b1_val { bdd.mk_var(b1) } else { -bdd.mk_var(b1) });
        s = bdd.apply_and(s, if b2_val { bdd.mk_var(b2) } else { -bdd.mk_var(b2) });
        s
    };

    let state_next = |n: u8| -> Ref {
        let b0_val = (n & 1) != 0;
        let b1_val = (n & 2) != 0;
        let b2_val = (n & 4) != 0;

        let mut s = bdd.one();
        s = bdd.apply_and(s, if b0_val { bdd.mk_var(b0_next) } else { -bdd.mk_var(b0_next) });
        s = bdd.apply_and(s, if b1_val { bdd.mk_var(b1_next) } else { -bdd.mk_var(b1_next) });
        s = bdd.apply_and(s, if b2_val { bdd.mk_var(b2_next) } else { -bdd.mk_var(b2_next) });
        s
    };

    // Create transition s_i -> s_{i+1}
    let transition = |from: u8, to: u8| -> Ref { bdd.apply_and(state(from), state_next(to)) };

    // Initial state: s0
    ts.set_initial(state(0));

    // Start with transition s0 -> s1
    let t01 = transition(0, 1);
    ts.set_transition(t01);

    println!("Phase 1: Initial system (s0 -> s1)");
    let start = Instant::now();
    let reach1 = ts.reachable();
    let time1 = start.elapsed();
    let count1 = count_states(&bdd, reach1, 3);
    println!("  Reachable states: {}", count1);
    println!("  Time: {:?}", time1);
    let r0 = is_reachable(&bdd, reach1, state(0));
    let r1 = is_reachable(&bdd, reach1, state(1));
    let r2 = is_reachable(&bdd, reach1, state(2));
    println!("  Reachable: s0={}, s1={}, s2={}", r0, r1, r2);
    assert_eq!(count1, 2, "Phase 1: Should reach exactly 2 states (s0, s1)");
    assert!(r0, "Phase 1: s0 must be reachable (initial state)");
    assert!(r1, "Phase 1: s1 must be reachable (via s0->s1)");
    assert!(!r2, "Phase 1: s2 must not be reachable yet");
    println!("  ✓ Assertions passed");
    println!();

    // Add transition s1 -> s2
    println!("Phase 2: Add transition s1 -> s2");
    let t12 = transition(1, 2);
    let start = Instant::now();
    let effect = ts.add_transitions(t12);
    let time2 = start.elapsed();
    println!("  Effect: {:?}", effect);

    let reach2 = ts.reachable();
    let count2 = count_states(&bdd, reach2, 3);
    println!("  Reachable states: {}", count2);
    println!("  Time: {:?}", time2);
    let r0_p2 = is_reachable(&bdd, reach2, state(0));
    let r1_p2 = is_reachable(&bdd, reach2, state(1));
    let r2_p2 = is_reachable(&bdd, reach2, state(2));
    let r3_p2 = is_reachable(&bdd, reach2, state(3));
    println!("  Reachable: s0={}, s1={}, s2={}, s3={}", r0_p2, r1_p2, r2_p2, r3_p2);
    assert_eq!(count2, 3, "Phase 2: Should reach exactly 3 states (s0, s1, s2)");
    assert!(r0_p2 && r1_p2 && r2_p2, "Phase 2: s0, s1, s2 must all be reachable");
    assert!(!r3_p2, "Phase 2: s3 must not be reachable yet");
    assert!(count2 > count1, "Phase 2: Reachable set should grow");
    println!("  ✓ Assertions passed");
    println!();

    // Add transitions s2 -> s3, s3 -> s4
    println!("Phase 3: Add transitions s2 -> s3 and s3 -> s4");
    let t23 = transition(2, 3);
    let t34 = transition(3, 4);
    let new_trans = bdd.apply_or(t23, t34);

    let start = Instant::now();
    let effect = ts.add_transitions(new_trans);
    let time3 = start.elapsed();
    println!("  Effect: {:?}", effect);

    let reach3 = ts.reachable();
    let count3 = count_states(&bdd, reach3, 3);
    println!("  Reachable states: {}", count3);
    println!("  Time: {:?}", time3);
    let r0_p3 = is_reachable(&bdd, reach3, state(0));
    let r1_p3 = is_reachable(&bdd, reach3, state(1));
    let r2_p3 = is_reachable(&bdd, reach3, state(2));
    let r3_p3 = is_reachable(&bdd, reach3, state(3));
    let r4_p3 = is_reachable(&bdd, reach3, state(4));
    let r5_p3 = is_reachable(&bdd, reach3, state(5));
    println!(
        "  Reachable: s0={}, s1={}, s2={}, s3={}, s4={}, s5={}",
        r0_p3, r1_p3, r2_p3, r3_p3, r4_p3, r5_p3
    );
    assert_eq!(count3, 5, "Phase 3: Should reach exactly 5 states (s0-s4)");
    assert!(r0_p3 && r1_p3 && r2_p3 && r3_p3 && r4_p3, "Phase 3: s0-s4 must all be reachable");
    assert!(!r5_p3, "Phase 3: s5 must not be reachable yet");
    assert!(count3 > count2, "Phase 3: Reachable set should continue to grow");
    println!("  ✓ Assertions passed");
    println!();

    // Add a disconnected transition s6 -> s7 (should not affect reachability from s0)
    println!("Phase 4: Add disconnected transition s6 -> s7");
    let t67 = transition(6, 7);

    let start = Instant::now();
    let effect = ts.add_transitions(t67);
    let time4 = start.elapsed();
    println!("  Effect: {:?}", effect);

    let reach4 = ts.reachable();
    let count4 = count_states(&bdd, reach4, 3);
    println!("  Reachable states: {}", count4);
    println!("  Time: {:?}", time4);
    let r6_p4 = is_reachable(&bdd, reach4, state(6));
    let r7_p4 = is_reachable(&bdd, reach4, state(7));
    println!("  s6 reachable: {}, s7 reachable: {}", r6_p4, r7_p4);
    assert_eq!(count4, 5, "Phase 4: Disconnected transition should not grow reachable set");
    assert!(!r6_p4 && !r7_p4, "Phase 4: s6, s7 must not be reachable (disconnected)");
    assert_eq!(count4, count3, "Phase 4: Reachable set should not change");
    println!("  ✓ Assertions passed");
    println!();

    // Connect s4 -> s6 to make s6, s7 reachable
    println!("Phase 5: Connect s4 -> s6 (makes s6, s7 reachable)");
    let t46 = transition(4, 6);

    let start = Instant::now();
    let effect = ts.add_transitions(t46);
    let time5 = start.elapsed();
    println!("  Effect: {:?}", effect);

    let reach5 = ts.reachable();
    let count5 = count_states(&bdd, reach5, 3);
    println!("  Reachable states: {}", count5);
    println!("  Time: {:?}", time5);
    let r6_p5 = is_reachable(&bdd, reach5, state(6));
    let r7_p5 = is_reachable(&bdd, reach5, state(7));
    println!("  s6 reachable: {}, s7 reachable: {}", r6_p5, r7_p5);
    assert_eq!(count5, 7, "Phase 5: Should now reach s0-s4 and s6-s7 (7 states total)");
    assert!(r6_p5 && r7_p5, "Phase 5: s6, s7 must now be reachable (connected via s4)");
    assert!(count5 > count4, "Phase 5: Reachable set should grow");
    println!("  ✓ Assertions passed");
    println!();

    // Summary
    println!("=== Summary ===");
    println!("Total incremental updates: 4");
    let final_count = count_states(&bdd, reach5, 3);
    println!("Final reachable states: {}", final_count);
    assert_eq!(final_count, 7, "Final state should contain 7 reachable states");

    let metrics = ts.metrics();
    println!("\nMetrics:");
    println!("  No-change operations: {}", metrics.no_change_count);
    println!("  Local-change operations: {}", metrics.local_change_count);
    println!("  Global rebuilds: {}", metrics.global_rebuild_count);
    println!("\n✓ All reachability tests passed!");
}

fn count_states(bdd: &Bdd, states: Ref, num_vars: usize) -> u64 {
    use num_traits::ToPrimitive;
    bdd.sat_count(states, num_vars).to_u64().unwrap_or(0)
}

fn is_reachable(bdd: &Bdd, reach: Ref, state: Ref) -> bool {
    !bdd.is_zero(bdd.apply_and(reach, state))
}
