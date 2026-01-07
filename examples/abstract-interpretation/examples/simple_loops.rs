//! Simple Loop Analysis Example.
//!
//! This example demonstrates the core concepts of abstract interpretation for loops:
//! 1. **Fixpoint Computation**: Iteratively approximating the loop invariant.
//! 2. **Widening**: Accelerating convergence to ensure termination (handling infinite loops).
//! 3. **Narrowing**: Refining the result after widening to improve precision.
//!
//! The analysis uses the **Interval Domain** to track the range of values for variables.

use abstract_interpretation::*;

fn main() {
    env_logger::init();
    println!("=== Simple Loop Analysis ===\n");

    let domain = IntervalDomain;
    let engine = FixpointEngine {
        domain: domain.clone(),
        widening_threshold: 3,
        narrowing_iterations: 2,
        max_iterations: 100,
    };

    example_counter_loop(&domain, &engine);
    example_countdown(&domain, &engine);
    example_unbounded_loop(&domain, &engine);

    println!("=== Analysis Complete ===");
}

/// Example 1: Counter loop - computes loop invariant
fn example_counter_loop(domain: &IntervalDomain, engine: &FixpointEngine<IntervalDomain>) {
    println!("Example 1: Counter Loop");
    println!("----------------------");
    println!("Program:");
    println!("  x = 0;");
    println!("  while (x < 10) {{");
    println!("    x = x + 1;");
    println!("  }}");
    println!();

    // Initial state before loop
    let mut init1 = IntervalElement::new();
    init1.set("x", Interval::constant(0));

    // States that enter the loop: must satisfy condition
    let entry1 = domain.assume(&init1, &NumExpr::var("x").lt(NumExpr::constant(10)));

    // Fixpoint: apply loop body repeatedly until convergence
    let f1 = |elem: &IntervalElement| {
        // Loop body: x = x + 1
        let x_int = elem.get("x");
        let incremented = Interval::new(x_int.low.add(&Bound::Finite(1)), x_int.high.add(&Bound::Finite(1)));
        let mut result = elem.clone();
        result.set("x", incremented);
        // Check loop condition: must satisfy x < 10 to continue
        let refined = domain.assume(&result, &NumExpr::var("x").lt(NumExpr::constant(10)));
        refined
    };

    let inside_loop = engine.lfp(entry1, f1);

    // True invariant: must hold at entry AND inside loop
    // Join: combine initial state with reachable states inside loop
    let init_x1 = init1.get("x");
    let inside_x1 = inside_loop.get("x");
    let loop_inv1 = init_x1.join(&inside_x1);

    println!("Loop invariant computed: x ∈ {}", loop_inv1);
    println!();

    // Verify the invariant holds everywhere

    // Check 1: Initial value is in the invariant
    let entry_value = 0;
    assert!(
        loop_inv1.contains(entry_value),
        "Entry state x={} must be in {}",
        entry_value,
        loop_inv1
    );
    println!("  ✓ At entry: x = {} ∈ {}", entry_value, loop_inv1);

    // Check 2: Inside-loop values are subset of invariant
    let inside_interval = Interval::new(Bound::Finite(1), Bound::Finite(9));
    assert!(
        inside_interval.is_subset_of(&loop_inv1),
        "Inside-loop {} must be ⊆ {}",
        inside_interval,
        loop_inv1
    );
    println!("  ✓ Inside loop: x ∈ {} ⊆ {}", inside_interval, loop_inv1);

    // Check 3: Exit value violates loop condition
    let exit_value = 10;
    assert!(
        !loop_inv1.contains(exit_value),
        "Exit state x={} must violate invariant {}",
        exit_value,
        loop_inv1
    );
    println!("  ✓ At exit: x ≥ {} violates x < 10 and {}", exit_value, loop_inv1);

    println!();
}

/// Example 2: Countdown loop - computes loop invariant from high value
fn example_countdown(domain: &IntervalDomain, engine: &FixpointEngine<IntervalDomain>) {
    println!("Example 2: Countdown Loop");
    println!("------------------------");
    println!("Program:");
    println!("  x = 100;");
    println!("  while (x > 0) {{");
    println!("    x = x - 1;");
    println!("  }}");
    println!();

    // Initial state before loop
    let mut init2 = IntervalElement::new();
    init2.set("x", Interval::constant(100));

    // States that enter the loop: must satisfy condition
    let entry2 = domain.assume(&init2, &NumExpr::var("x").gt(NumExpr::constant(0)));

    // Fixpoint: apply loop body repeatedly until convergence
    let f2 = |elem: &IntervalElement| {
        // Loop body: x = x - 1
        let x_int = elem.get("x");
        let decremented = Interval::new(x_int.low.sub(&Bound::Finite(1)), x_int.high.sub(&Bound::Finite(1)));
        let mut result = elem.clone();
        result.set("x", decremented);
        // Check loop condition: must satisfy x > 0 to continue
        let refined = domain.assume(&result, &NumExpr::var("x").gt(NumExpr::constant(0)));
        refined
    };

    let inside_loop = engine.lfp(entry2, f2);

    // True invariant: must hold at entry AND inside loop
    // Join: combine initial state with reachable states inside loop
    let init_x2 = init2.get("x");
    let inside_x2 = inside_loop.get("x");
    let loop_inv2 = init_x2.join(&inside_x2);

    println!("Loop invariant computed: x ∈ {}", loop_inv2);
    println!();

    // Verify the invariant holds everywhere

    // Check 1: Initial value is in the invariant
    let entry_value = 100;
    assert!(
        loop_inv2.contains(entry_value),
        "Entry state x={} must be in {}",
        entry_value,
        loop_inv2
    );
    println!("  ✓ At entry: x = {} ∈ {}", entry_value, loop_inv2);

    // Check 2: Inside-loop values are subset of invariant
    let inside_interval = Interval::new(Bound::Finite(1), Bound::Finite(99));
    assert!(
        inside_interval.is_subset_of(&loop_inv2),
        "Inside-loop {} must be ⊆ {}",
        inside_interval,
        loop_inv2
    );
    println!("  ✓ Inside loop: x ∈ {} ⊆ {}", inside_interval, loop_inv2);

    // Check 3: Exit value violates loop condition
    let exit_value = 0;
    assert!(
        !loop_inv2.contains(exit_value),
        "Exit state x={} must violate invariant {}",
        exit_value,
        loop_inv2
    );
    println!("  ✓ At exit: x ≤ {} violates x > 0 and {}", exit_value, loop_inv2);

    println!();
}

/// Example 3: Unbounded loop - demonstrates widening to +∞
fn example_unbounded_loop(_domain: &IntervalDomain, engine: &FixpointEngine<IntervalDomain>) {
    println!("Example 3: Unbounded Loop (Infinite)");
    println!("------------------------------------");
    println!("Program:");
    println!("  x = 0;");
    println!("  while (true) {{");
    println!("    x = x + 1;");
    println!("  }}");
    println!();

    // Initial state before loop
    let mut init3 = IntervalElement::new();
    init3.set("x", Interval::constant(0));

    // Fixpoint: apply loop body repeatedly until convergence
    // Note: No loop condition to refine, so widening must occur to ensure termination
    let f3 = |elem: &IntervalElement| {
        // Loop body: x = x + 1
        let x_int = elem.get("x");
        let incremented = Interval::new(x_int.low.add(&Bound::Finite(1)), x_int.high.add(&Bound::Finite(1)));
        let mut result = elem.clone();
        result.set("x", incremented);
        result
    };

    let inside_loop = engine.lfp(init3.clone(), f3);

    // True invariant: must hold at entry AND inside loop
    // For infinite loops, join entry with reachable states
    let init_x3 = init3.get("x");
    let inside_x3 = inside_loop.get("x");
    let loop_inv3 = init_x3.join(&inside_x3);

    println!("Loop invariant computed: x ∈ {}", loop_inv3);
    println!("This loop never terminates, so x grows unboundedly.");
    println!();

    // Verify widening occurred and invariant is correct

    // Check 1: Initial value is in the invariant
    let entry_value = 0;
    assert!(
        loop_inv3.contains(entry_value),
        "Entry state x={} must be in {}",
        entry_value,
        loop_inv3
    );
    println!("  ✓ At entry: x = {} ∈ {}", entry_value, loop_inv3);

    // Check 2: Inside-loop values are subset of invariant
    assert!(
        inside_x3.is_subset_of(&loop_inv3),
        "Inside-loop {} must be ⊆ {}",
        inside_x3,
        loop_inv3
    );
    println!("  ✓ Inside loop: x ∈ {} ⊆ {}", inside_x3, loop_inv3);

    // Check 3: Infinite loop - no exit condition, grows unbounded
    assert!(matches!(loop_inv3.high, Bound::PosInf), "x should grow to +∞");
    println!("  ✓ No exit: loop never terminates, x → +∞");

    println!();
}
