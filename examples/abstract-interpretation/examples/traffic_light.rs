//! Traffic Light Controller Analysis Example.
//!
//! This example demonstrates **Control-Sensitive Analysis** for a state machine:
//! a simple 3-state traffic light (RED → GREEN → YELLOW).
//!
//! **Safety Properties Verified**:
//! 1. **Mutual Exclusion**: The light is never RED and GREEN simultaneously.
//! 2. **State-Dependent Invariants**:
//!    - RED: Timer ∈ [0, 60]
//!    - GREEN: Timer ∈ [0, 45]
//!    - YELLOW: Timer ∈ [0, 5]
//!
//! **Key Insight**:
//! Path-insensitive analysis would merge the timer intervals to [0, 60] for all states,
//! losing the critical safety property that "YELLOW light duration ≤ 5".
//! The BDD-based analysis maintains this precision.

use std::rc::Rc;

use abstract_interpretation::*;

fn main() {
    println!("=== Traffic Light Controller Analysis ===");
    println!();

    // System description
    println!("SYSTEM DESCRIPTION:");
    println!("  A traffic light controller with 3 states cycling:");
    println!("    RED → GREEN → YELLOW → RED (repeat)");
    println!();
    println!("  Variables:");
    println!("    • state_bit0, state_bit1: 2-bit state encoding");
    println!("    • timer: Countdown timer for each state");
    println!();

    println!("SAFETY PROPERTIES TO VERIFY:");
    println!("  P1: Light is always in exactly one state {{RED, GREEN, YELLOW}}");
    println!("  P2: Timer bounds depend on current state:");
    println!("      - RED state: timer ∈ [0, 60]");
    println!("      - GREEN state: timer ∈ [0, 45]");
    println!("      - YELLOW state: timer ∈ [0, 5]");
    println!("  P3: Mutual exclusion: never RED and GREEN simultaneously");
    println!();

    example_path_insensitive();
    example_path_sensitive();
}

/// Example 1: Path-insensitive analysis
fn example_path_insensitive() {
    println!("Example 1: Path-Insensitive Analysis");
    println!("-------------------------------------");
    println!();

    let domain = IntervalDomain;

    // RED state: timer ∈ [0, 60]
    let red_state = domain.interval("timer", 0, 60);

    // GREEN state: timer ∈ [0, 45]
    let green_state = domain.interval("timer", 0, 45);

    // YELLOW state: timer ∈ [0, 5]
    let yellow_state = domain.interval("timer", 0, 5);

    // Join all states (path-insensitive)
    let mut merged = red_state;
    merged = domain.join(&merged, &green_state);
    merged = domain.join(&merged, &yellow_state);

    println!("Individual states:");
    println!("  RED:    timer ∈ [0, 60]");
    println!("  GREEN:  timer ∈ [0, 45]");
    println!("  YELLOW: timer ∈ [0, 5]");

    println!();
    println!("After merging all states:");
    if let Some((low, high)) = domain.get_bounds(&merged, "timer") {
        println!("  timer ∈ [{}, {}]", low, high);
    }

    println!();
    println!("⚠️ IMPRECISION: Cannot determine which state the light is in!");
    println!("⚠️ Lost precision: timer could be 60 in YELLOW state (impossible!)");
    println!("⚠️ Cannot verify: \"YELLOW state has timer ≤ 5\"");
    println!();
}

/// Example 2: Path-sensitive analysis
fn example_path_sensitive() {
    println!("Example 2: Path-Sensitive Analysis (BDD Control)");
    println!("------------------------------------------------");
    println!();

    let control_domain = Rc::new(BddControlDomain::new());
    let numeric_domain = Rc::new(IntervalDomain);
    let product = ControlSensitiveProduct::new(control_domain.clone(), numeric_domain.clone());

    // Allocate control variables for 3 states (need 2 bits)
    let state_bit0 = control_domain.allocate_var("state_bit0");
    let state_bit1 = control_domain.allocate_var("state_bit1");

    // State encoding:
    // RED (0):    bit1=0, bit0=0
    // GREEN (1):  bit1=0, bit0=1
    // YELLOW (2): bit1=1, bit0=0
    // (unused):   bit1=1, bit0=1

    println!("Control variables allocated:");
    println!("  state_bit0 (id: {})", state_bit0);
    println!("  state_bit1 (id: {})", state_bit1);
    println!();
    println!("State encoding:");
    println!("  RED (00):    bit1=0, bit0=0");
    println!("  GREEN (01):  bit1=0, bit0=1");
    println!("  YELLOW (10): bit1=1, bit0=0");

    // Create control states for each light color
    // RED: bit1=0, bit0=0
    let ctrl_red = control_domain.mk_var_false("state_bit1");
    let ctrl_red = control_domain.and(&ctrl_red, &control_domain.mk_var_false("state_bit0"));

    // GREEN: bit1=0, bit0=1
    let ctrl_green = control_domain.mk_var_false("state_bit1");
    let ctrl_green = control_domain.and(&ctrl_green, &control_domain.mk_var_true("state_bit0"));

    // YELLOW: bit1=1, bit0=0
    let ctrl_yellow = control_domain.mk_var_true("state_bit1");
    let ctrl_yellow = control_domain.and(&ctrl_yellow, &control_domain.mk_var_false("state_bit0"));

    // Create numeric states with precise timer bounds
    let num_red = numeric_domain.interval("timer", 0, 60);
    let num_green = numeric_domain.interval("timer", 0, 45);
    let num_yellow = numeric_domain.interval("timer", 0, 5);

    // Create control-sensitive elements
    let state_red = product.mk_single_partition(ctrl_red.clone(), num_red);
    let state_green = product.mk_single_partition(ctrl_green.clone(), num_green);
    let state_yellow = product.mk_single_partition(ctrl_yellow.clone(), num_yellow);

    println!();
    println!("--- Created States ---");
    println!("RED state (00):    timer ∈ [0, 60]");
    println!("GREEN state (01):  timer ∈ [0, 45]");
    println!("YELLOW state (10): timer ∈ [0, 5]");

    // Join all states (but maintain partitions!)
    let mut all_states = state_red;
    all_states = product.join(&all_states, &state_green);
    all_states = product.join(&all_states, &state_yellow);

    println!();
    println!("--- After Join (Path-Sensitive) ---");
    println!("Number of partitions: {} (one per light state)", all_states.partition_count());
    println!();

    // Verify and display actual timer bounds from each partition
    println!("Each partition maintains precise timer bounds:");

    // RED: timer ∈ [0, 60]
    if let Some(num_state) = all_states.get(&ctrl_red) {
        if let Some((low, high)) = numeric_domain.get_bounds(num_state, "timer") {
            assert_eq!((low, high), (0, 60), "RED state: timer should be [0,60]");
            println!("  RED partition:    timer ∈ [{}, {}]", low, high);
        }
    } else {
        panic!("RED partition missing!");
    }

    // GREEN: timer ∈ [0, 45]
    if let Some(num_state) = all_states.get(&ctrl_green) {
        if let Some((low, high)) = numeric_domain.get_bounds(num_state, "timer") {
            assert_eq!((low, high), (0, 45), "GREEN state: timer should be [0,45]");
            println!("  GREEN partition:  timer ∈ [{}, {}]", low, high);
        }
    } else {
        panic!("GREEN partition missing!");
    }

    // YELLOW: timer ∈ [0, 5]
    if let Some(num_state) = all_states.get(&ctrl_yellow) {
        if let Some((low, high)) = numeric_domain.get_bounds(num_state, "timer") {
            assert_eq!((low, high), (0, 5), "YELLOW state: timer should be [0,5]");
            println!("  YELLOW partition: timer ∈ [{}, {}]", low, high);
        }
    } else {
        panic!("YELLOW partition missing!");
    }

    // Verify safety properties
    println!();
    println!("=== Safety Property Verification ===");
    println!();

    // P1: Verify partition count
    assert_eq!(all_states.partition_count(), 3, "Should have 3 partitions (one per light state)");
    println!("✅ P1: Light is always in exactly one of 3 states");

    // Check mutual exclusion: RED and GREEN are disjoint
    let red_and_green = control_domain.and(&ctrl_red, &ctrl_green);
    assert!(
        control_domain.is_bottom(&red_and_green),
        "RED and GREEN should be mutually exclusive"
    );
    println!("✅ P3: Mutual exclusion verified: RED ∧ GREEN = ⊥ (impossible)");

    // P2: Timer bounds are verified above (assertions passed)
    println!("✅ P2: Timer bounds verified per state:");
    println!("      RED: timer ∈ [0, 60]");
    println!("      GREEN: timer ∈ [0, 45]");
    println!("      YELLOW: timer ∈ [0, 5]");

    println!();
    println!("=== Precision Comparison ===");
    println!();
    println!("Path-Insensitive:");
    println!("  • Single merged state: timer ∈ [0, 60]");
    println!("  • Cannot verify YELLOW timer bound (timer ≤ 5)");
    println!("  • Lost information about current state");
    println!();
    println!("Path-Sensitive (BDD Control):");
    println!("  • 3 separate partitions: one per light color");
    println!("  • Precise timer bounds: RED [0,60], GREEN [0,45], YELLOW [0,5]");
    println!("  • All safety properties verified!");
    println!("  • Mutual exclusion guaranteed by disjoint control states");

    println!();
    println!("=== Key Insights ===");
    println!();
    println!("• BDD encodes 3 states using 2 Boolean variables");
    println!("• Each state maintains its own numeric invariant (timer bound)");
    println!("• Control-sensitive product prevents false alarms");
    println!("• Essential for verifying state-dependent properties");
}
