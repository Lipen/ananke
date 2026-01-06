//! Mode-Based Controller Analysis Example.
//!
//! This example demonstrates the advantages of **Control-Sensitive Analysis** (using BDDs)
//! for embedded systems with multiple operating modes.
//!
//! The controller transitions between 4 modes:
//! - **INIT**: Startup mode (Actuator OFF).
//! - **READY**: Ready to activate (Actuator OFF).
//! - **ACTIVE**: System running (Actuator ON).
//! - **ERROR**: Fault detected (Actuator OFF).
//!
//! **The Challenge**:
//! A standard path-insensitive analysis (like Interval Domain alone) would merge all states,
//! concluding that `Actuator` can be ON or OFF in *any* mode. This leads to false alarms
//! (e.g., "Actuator might be ON in ERROR mode").
//!
//! **The Solution**:
//! By partitioning the state space with BDDs (Control Domain), we maintain separate
//! invariants for each mode, proving that `Actuator` is strictly OFF in ERROR mode.

use std::rc::Rc;

use abstract_interpretation::*;

fn main() {
    println!("=== Mode-Based Controller Analysis ===\n");

    // System description
    println!("SYSTEM DESCRIPTION:");
    println!("  An embedded controller with 4 operating modes:");
    println!("    • INIT (00):   Initial startup mode");
    println!("    • READY (01):  Ready to activate");
    println!("    • ACTIVE (10): System is active, actuator enabled");
    println!("    • ERROR (11):  Error state, actuator disabled");
    println!();
    println!("  Variables:");
    println!("    • mode_bit0, mode_bit1: 2-bit mode encoding");
    println!("    • sensor: Input sensor reading");
    println!("    • actuator: Output actuator (0=off, 1=on)");
    println!();

    println!("SAFETY PROPERTIES TO VERIFY:");
    println!("  P1: Mode is always one of {{INIT, READY, ACTIVE, ERROR}}");
    println!("  P2: Actuator is always 0 or 1");
    println!("  P3: In ERROR mode, actuator must be 0");
    println!("  P4: Actuator can only be 1 in ACTIVE mode");
    println!();
    println!("=======================================================");
    println!();

    // Run both path-insensitive and path-sensitive analysis
    analyze_path_insensitive();
    println!("\n=======================================================\n");
    analyze_path_sensitive();

    println!("\n=======================================================");
    println!("   Analysis Complete");
    println!("=======================================================\n");
}

/// Path-insensitive analysis: merges all control states
fn analyze_path_insensitive() {
    println!("--- Path-Insensitive Analysis ---");
    println!();

    let domain = IntervalDomain;

    println!("Initial state:");
    println!("  mode = INIT");
    println!("  sensor ∈ [0, 0]");
    println!("  actuator = 0");

    // Simulate mode transitions using interval domain
    // In path-insensitive analysis, we lose track of which mode we're in

    // INIT state: mode=0, actuator=0
    let init_state = domain.interval("actuator", 0, 0);

    // READY state: mode=1, actuator=0
    let ready_state = domain.interval("actuator", 0, 0);

    // ACTIVE state: mode=2, actuator=1
    let active_state = domain.interval("actuator", 1, 1);

    // ERROR state: mode=3, actuator=0
    let error_state = domain.interval("actuator", 0, 0);

    // Join all states (path-insensitive merge)
    let mut merged = init_state;
    merged = domain.join(&merged, &ready_state);
    merged = domain.join(&merged, &active_state);
    merged = domain.join(&merged, &error_state);

    println!();
    println!("After merging all control paths:");
    println!("  mode ∈ {{INIT, READY, ACTIVE, ERROR}} (all modes possible)");

    if let Some((low, high)) = domain.get_bounds(&merged, "actuator") {
        println!("  actuator ∈ [{}, {}]", low, high);
    }

    println!();
    println!("⚠️ IMPRECISION: Cannot verify that actuator=1 only in ACTIVE mode!");
    println!("⚠️ False alarm: actuator might be 1 in ERROR mode (not actually possible)");
}

/// Path-sensitive analysis: maintains separate states per control mode
fn analyze_path_sensitive() {
    println!("--- Path-Sensitive Analysis (BDD Control) ---");
    println!();

    let control_domain = Rc::new(BddControlDomain::new());
    let numeric_domain = Rc::new(IntervalDomain);
    let product = ControlSensitiveProduct::new(control_domain.clone(), numeric_domain.clone());

    // Allocate control variables for mode encoding
    // We need 2 bits to encode 4 modes: mode_bit0, mode_bit1
    let mode_bit0 = control_domain.allocate_var("mode_bit0");
    let mode_bit1 = control_domain.allocate_var("mode_bit1");

    // Mode encoding:
    // INIT (0):   bit1=0, bit0=0
    // READY (1):  bit1=0, bit0=1
    // ACTIVE (2): bit1=1, bit0=0
    // ERROR (3):  bit1=1, bit0=1

    println!("Control variables allocated:");
    println!("  mode_bit0 (id: {}) - least significant bit", mode_bit0);
    println!("  mode_bit1 (id: {}) - most significant bit", mode_bit1);

    // Create control states for each mode
    // INIT: bit1=0, bit0=0
    let ctrl_init = control_domain.mk_var_false("mode_bit1");
    let ctrl_init = control_domain.and(&ctrl_init, &control_domain.mk_var_false("mode_bit0"));

    // READY: bit1=0, bit0=1
    let ctrl_ready = control_domain.mk_var_false("mode_bit1");
    let ctrl_ready = control_domain.and(&ctrl_ready, &control_domain.mk_var_true("mode_bit0"));

    // ACTIVE: bit1=1, bit0=0
    let ctrl_active = control_domain.mk_var_true("mode_bit1");
    let ctrl_active = control_domain.and(&ctrl_active, &control_domain.mk_var_false("mode_bit0"));

    // ERROR: bit1=1, bit0=1
    let ctrl_error = control_domain.mk_var_true("mode_bit1");
    let ctrl_error = control_domain.and(&ctrl_error, &control_domain.mk_var_true("mode_bit0"));

    // Create numeric states for each mode
    // INIT: actuator=0
    let num_init = numeric_domain.interval("actuator", 0, 0);

    // READY: actuator=0
    let num_ready = numeric_domain.interval("actuator", 0, 0);

    // ACTIVE: actuator=1
    let num_active = numeric_domain.interval("actuator", 1, 1);

    // ERROR: actuator=0
    let num_error = numeric_domain.interval("actuator", 0, 0);

    // Create control-sensitive elements for each mode
    let state_init = product.mk_single_partition(ctrl_init.clone(), num_init);
    let state_ready = product.mk_single_partition(ctrl_ready.clone(), num_ready);
    let state_active = product.mk_single_partition(ctrl_active.clone(), num_active);
    let state_error = product.mk_single_partition(ctrl_error.clone(), num_error);

    println!();
    println!("Mode States Created:");
    println!("  INIT (00):   actuator ∈ [0,0]");
    println!("  READY (01):  actuator ∈ [0,0]");
    println!("  ACTIVE (10): actuator ∈ [1,1] ✓");
    println!("  ERROR (11):  actuator ∈ [0,0] ✓");

    // Join all reachable states
    let mut all_states = state_init;
    all_states = product.join(&all_states, &state_ready);
    all_states = product.join(&all_states, &state_active);
    all_states = product.join(&all_states, &state_error);

    println!();
    println!("After joining all states:");
    println!("  Number of partitions: {} (one per mode)", all_states.partition_count());
    println!("  Control states remain distinct (not merged!)");

    println!();
    println!("--- Verification ---");

    // Verify partition count
    assert_eq!(all_states.partition_count(), 4, "Should have 4 partitions (one per mode)");
    println!("✅ P1: All 4 modes represented as separate partitions");

    // Verify each mode has the correct actuator bounds
    // INIT: actuator = 0
    if let Some(num_state) = all_states.get(&ctrl_init) {
        if let Some((low, high)) = numeric_domain.get_bounds(num_state, "actuator") {
            assert_eq!((low, high), (0, 0), "INIT mode: actuator should be [0,0]");
            println!("✅ P2: In INIT mode: actuator = 0");
        }
    } else {
        panic!("INIT mode partition missing!");
    }

    // READY: actuator = 0
    if let Some(num_state) = all_states.get(&ctrl_ready) {
        if let Some((low, high)) = numeric_domain.get_bounds(num_state, "actuator") {
            assert_eq!((low, high), (0, 0), "READY mode: actuator should be [0,0]");
            println!("✅ P2: In READY mode: actuator = 0");
        }
    } else {
        panic!("READY mode partition missing!");
    }

    // ACTIVE: actuator = 1
    if let Some(num_state) = all_states.get(&ctrl_active) {
        if let Some((low, high)) = numeric_domain.get_bounds(num_state, "actuator") {
            assert_eq!((low, high), (1, 1), "ACTIVE mode: actuator should be [1,1]");
            println!("✅ P4: In ACTIVE mode: actuator = 1 (only mode where actuator can be 1)");
        }
    } else {
        panic!("ACTIVE mode partition missing!");
    }

    // ERROR: actuator = 0
    if let Some(num_state) = all_states.get(&ctrl_error) {
        if let Some((low, high)) = numeric_domain.get_bounds(num_state, "actuator") {
            assert_eq!((low, high), (0, 0), "ERROR mode: actuator should be [0,0]");
            println!("✅ P3: In ERROR mode: actuator = 0");
        }
    } else {
        panic!("ERROR mode partition missing!");
    }

    // Verify mutual exclusion by checking control states are disjoint
    let active_and_error = control_domain.and(&ctrl_active, &ctrl_error);
    assert!(
        control_domain.is_bottom(&active_and_error),
        "ACTIVE and ERROR should be mutually exclusive"
    );
    println!("✅ Mutual exclusion verified: ACTIVE ∧ ERROR = ⊥");

    println!("✅ All safety properties verified!");
    println!("✓ No false alarms: BDD partitioning maintains precise invariants");
    println!();
    println!("=== Precision Comparison ===");
    println!("Path-Insensitive: actuator ∈ [0,1] for all modes (IMPRECISE)");
    println!("Path-Sensitive:   actuator ∈ [1,1] in ACTIVE, [0,0] elsewhere (PRECISE)");

    println!();
    println!("=== Key Insights ===");
    println!("• BDD control domain tracks mode transitions precisely");
    println!("• Each mode has its own numeric invariant (partition)");
    println!("• Safety property \"actuator=1 only in ACTIVE\" is verified");
    println!("• Path-insensitive analysis would report false alarm");
}
