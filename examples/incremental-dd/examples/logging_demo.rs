//! Demonstration of debug logging in incremental operations.
//!
//! Run with: `RUST_LOG=info,incremental_dd=debug cargo run --example logging_demo`

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use incremental_dd::incremental_ts::{IncrementalReachabilityFixpoint, IncrementalTransSystem};
use incremental_dd::traits::IncrementalFixpoint;
use model_checking::transition::Var;

fn main() {
    // Initialize logger
    env_logger::init();

    log::info!("=== Incremental Reachability Demo ===");

    let bdd = Rc::new(Bdd::default());
    let mut ts = IncrementalTransSystem::new(bdd.clone());

    // Create a 3-state system: s0 -> s1 -> s2
    let (s0_var, s0_next) = ts.declare_var(Var::new("b0"));
    let (s1_var, s1_next) = ts.declare_var(Var::new("b1"));

    // States
    let s00 = bdd.apply_and(-bdd.mk_var(s0_var), -bdd.mk_var(s1_var));
    let s01 = bdd.apply_and(-bdd.mk_var(s0_var), bdd.mk_var(s1_var));
    let _s10 = bdd.apply_and(bdd.mk_var(s0_var), -bdd.mk_var(s1_var));

    // Next-state encodings
    let s01_next = bdd.apply_and(-bdd.mk_var(s0_next), bdd.mk_var(s1_next));
    let s10_next = bdd.apply_and(bdd.mk_var(s0_next), -bdd.mk_var(s1_next));

    // Set initial state
    ts.set_initial(s00);
    log::info!("Initial state set to s00");

    // Transitions: s00 -> s01
    let t1 = bdd.apply_and(s00, s01_next);
    ts.set_transition(t1);
    log::info!("Initial transition added: s00 -> s01");

    // Create fixpoint engine and compute
    let mut fp = IncrementalReachabilityFixpoint::new(ts);
    log::info!("Created fixpoint engine");

    let reach1 = fp.compute();
    log::info!(
        "First fixpoint computed: reachable states = {}, iterations = {}",
        bdd.size(reach1),
        fp.metrics().full_iterations
    );

    // Now add a new transition: s01 -> s10
    log::info!("\n=== Adding new transition: s01 -> s10 ===");
    let t2 = bdd.apply_and(s01, s10_next);
    let update = fp.add_transitions(t2);
    log::info!("Fixpoint updated: {:?}", update);

    let reach2 = fp.current();
    log::info!("New fixpoint: reachable states = {}", bdd.size(reach2));

    log::info!("\n=== Demo complete ===");
}
