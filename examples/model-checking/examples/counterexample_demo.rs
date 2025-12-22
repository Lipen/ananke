//! Demonstration of enhanced counterexample visualization features.
//!
//! This example shows:
//! - ASCII trace diagrams for counterexamples
//! - State annotations and labels
//! - XAI-style explanations for property violations
//! - Custom state and transition interpreters

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use model_checking::*;

fn header(s: &str) {
    println!("{}", s);
    println!("{}", "─".repeat(s.len()));
    println!();
}

fn main() {
    println!("══════════════════════════════════════");
    println!("  Counterexample Visualization Demos  ");
    println!("══════════════════════════════════════");
    println!();

    demo_linear_counterexample();
    demo_lasso_counterexample();
    demo_xai_explanations();
}

/// Demo 1: Linear counterexample with ASCII visualization
fn demo_linear_counterexample() {
    header("Demo 1: Linear Counterexample - Traffic Light Violation");
    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd);

    // Two lights: north-south (ns) and east-west (ew)
    // Each can be: 0=red, 1=green
    let ns = Var::new("ns");
    let ew = Var::new("ew");
    ts.declare_var(ns.clone());
    ts.declare_var(ew.clone());

    let ns_pres = ts.var_manager().get_present(&ns).unwrap();
    let ew_pres = ts.var_manager().get_present(&ew).unwrap();
    let ns_bdd = ts.bdd().mk_var(ns_pres);
    let ew_bdd = ts.bdd().mk_var(ew_pres);

    // Initial: ns=green(1), ew=red(0)
    let initial = ts.bdd().apply_and(ns_bdd, ts.bdd().apply_not(ew_bdd));
    ts.set_initial(initial);

    // Transitions (with a bug that allows both green):
    // - ns=1, ew=0 -> ns=0, ew=1 (correct)
    // - ns=0, ew=1 -> ns=1, ew=0 (correct)
    // - ns=1, ew=0 -> ns=1, ew=1 (BUG: both green!)
    let trans1 = {
        // From ns=1, ew=0 to ns=0, ew=1
        let from = ts.bdd().apply_and(ns_bdd, ts.bdd().apply_not(ew_bdd));
        let ns_trans = ts.assign_var(&ns, ts.bdd().zero());
        let ew_trans = ts.assign_var(&ew, ts.bdd().one());
        let to = ts.build_transition(&[ns_trans, ew_trans]);
        ts.bdd().apply_and(from, to)
    };
    let trans2 = {
        // From ns=0, ew=1 to ns=1, ew=0
        let from = ts.bdd().apply_and(ts.bdd().apply_not(ns_bdd), ew_bdd);
        let ns_trans = ts.assign_var(&ns, ts.bdd().one());
        let ew_trans = ts.assign_var(&ew, ts.bdd().zero());
        let to = ts.build_transition(&[ns_trans, ew_trans]);
        ts.bdd().apply_and(from, to)
    };
    let trans_bug = {
        // BUG: From ns=1, ew=0 to ns=1, ew=1 (both green!)
        let from = ts.bdd().apply_and(ns_bdd, ts.bdd().apply_not(ew_bdd));
        let ns_trans = ts.assign_var(&ns, ts.bdd().one());
        let ew_trans = ts.assign_var(&ew, ts.bdd().one());
        let to = ts.build_transition(&[ns_trans, ew_trans]);
        ts.bdd().apply_and(from, to)
    };
    let transition = ts.bdd().apply_or(ts.bdd().apply_or(trans1, trans2), trans_bug);
    ts.set_transition(transition);

    // Labels
    let both_green = ts.bdd().apply_and(ns_bdd, ew_bdd);
    let safe = ts.bdd().apply_not(both_green);
    ts.add_label("safe".to_string(), safe);
    ts.add_label("collision_risk".to_string(), both_green);

    let ts = Rc::new(ts);
    let gen = CounterexampleGenerator::new(ts.clone());

    // Generate counterexample to safety
    println!("Checking: AG(safe) - No collision should ever be possible\n");

    if let Some(cex) = gen.generate_linear(both_green) {
        println!("Found violation! Generating visualization...\n");

        // Standard display
        println!("── Standard Display ───────────────────────────────────────────────");
        println!("{}", cex);

        // Annotated
        let annotated = cex.clone().with_annotations();
        println!("── Annotated Display ──────────────────────────────────────────────");
        println!("{}", annotated);

        // Full visualization with labels
        println!("── ASCII Trace Diagram ────────────────────────────────────────────");
        let vis = cex
            .visualize()
            .with_label("safe", |s| {
                let ns = s.get("ns").unwrap_or(false);
                let ew = s.get("ew").unwrap_or(false);
                !(ns && ew)
            })
            .with_label("ns_green", |s| s.get("ns").unwrap_or(false))
            .with_label("ew_green", |s| s.get("ew").unwrap_or(false));
        println!("{}", vis.render());

        // Compact version
        println!("── Compact Trace ──────────────────────────────────────────────────");
        let compact = cex.clone().with_annotations().visualize().compact().hide_labels();
        println!("{}", compact.render());
    }
}

/// Demo 2: Lasso counterexample for liveness violation
fn demo_lasso_counterexample() {
    header("Demo 2: Lasso Counterexample - Starvation");

    // Two processes competing for a resource
    // Process 0 can starve process 1
    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd);

    // req0, req1 = request flags, granted = which process has resource (0 or 1)
    let req0 = Var::new("req0");
    let req1 = Var::new("req1");
    let granted = Var::new("granted");
    ts.declare_var(req0.clone());
    ts.declare_var(req1.clone());
    ts.declare_var(granted.clone());

    let req0_pres = ts.var_manager().get_present(&req0).unwrap();
    let req1_pres = ts.var_manager().get_present(&req1).unwrap();
    let granted_pres = ts.var_manager().get_present(&granted).unwrap();
    let req0_bdd = ts.bdd().mk_var(req0_pres);
    let req1_bdd = ts.bdd().mk_var(req1_pres);
    let granted_bdd = ts.bdd().mk_var(granted_pres);

    // Initial: both requesting, granted=0
    let initial = ts.bdd().mk_cube([req0_pres.pos(), req1_pres.pos(), granted_pres.neg()]);
    ts.set_initial(initial);

    // Transitions (unfair arbiter that always picks process 0):
    // If both request, always grant 0
    // Toggle between 0 and 0 (never granting 1!)
    let trans = {
        let both_req = ts.bdd().apply_and(req0_bdd, req1_bdd);
        // When both request, stay with granted=0 or keep it at 0
        let granted_trans = ts.assign_var(&granted, ts.bdd().zero());
        // Requests stay active
        let req0_trans = ts.assign_var(&req0, req0_bdd);
        let req1_trans = ts.assign_var(&req1, req1_bdd);
        let to = ts.build_transition(&[granted_trans, req0_trans, req1_trans]);
        ts.bdd().apply_and(both_req, to)
    };
    ts.set_transition(trans);

    // Label
    let p1_granted = granted_bdd; // granted=1 means p1 has it
    ts.add_label("p1_granted".to_string(), p1_granted);

    let ts = Rc::new(ts);
    let gen = CounterexampleGenerator::new(ts.clone());

    // Find infinite loop where p1 is never granted
    // EG(¬p1_granted) = states from which we can always avoid granting p1
    let not_granted = ts.bdd().apply_not(p1_granted);
    let reachable = ts.reachable();
    let eg_not_granted = ts.bdd().apply_and(reachable, not_granted);

    println!("Checking: AG(req1 -> AF(p1_granted)) - If p1 requests, eventually granted\n");

    if let Some(cex) = gen.generate_lasso(eg_not_granted) {
        println!("Found starvation! Process 1 never gets the resource.\n");

        // Standard display
        println!("── Standard Display ───────────────────────────────────────────────");
        println!("{}", cex);

        // Full visualization
        println!("── ASCII Trace Diagram ────────────────────────────────────────────");
        let vis = cex
            .visualize()
            .with_label("req0", |s| s.get("req0").unwrap_or(false))
            .with_label("req1", |s| s.get("req1").unwrap_or(false))
            .with_label("p1_granted", |s| s.get("granted").unwrap_or(false));
        println!("{}", vis.render());
    }
}

/// Demo 3: XAI-style explanations
fn demo_xai_explanations() {
    header("Demo 3: XAI-Style Property Violation Explanations");
    println!("────────────────────────────────────────────────");
    println!();

    // Simple counter that overflows
    let bdd = Rc::new(Bdd::default());
    let mut ts = TransitionSystem::new(bdd);

    let b0 = Var::new("b0");
    let b1 = Var::new("b1");
    ts.declare_var(b0.clone());
    ts.declare_var(b1.clone());

    let b0_pres = ts.var_manager().get_present(&b0).unwrap();
    let b1_pres = ts.var_manager().get_present(&b1).unwrap();
    let b0_bdd = ts.bdd().mk_var(b0_pres);
    let b1_bdd = ts.bdd().mk_var(b1_pres);

    // Initial: 00
    let initial = ts.bdd().mk_cube([b0_pres.neg(), b1_pres.neg()]);
    ts.set_initial(initial);

    // Counter: 00 -> 01 -> 10 -> 11 (overflow)
    let b0_trans = ts.assign_var(&b0, ts.bdd().apply_not(b0_bdd));
    let b1_trans = ts.assign_var(&b1, ts.bdd().apply_xor(b0_bdd, b1_bdd));
    let trans = ts.build_transition(&[b0_trans, b1_trans]);
    ts.set_transition(trans);

    // Overflow = 11
    let overflow = ts.bdd().apply_and(b0_bdd, b1_bdd);
    ts.add_label("overflow".to_string(), overflow);

    let ts = Rc::new(ts);
    let gen = CounterexampleGenerator::new(ts.clone());

    println!("Checking: AG(¬overflow) - Counter should never overflow");
    println!("         where: overflow ≡ (b0 ∧ b1), i.e., counter value = 3\n");

    if let Some(cex) = gen.generate_linear(overflow) {
        println!("Found overflow! Building explanation...\n");

        // Build XAI-style explanation with custom interpreters
        let explanation = ExplanationBuilder::new(&cex, "AG(¬overflow)")
            .with_state_interpreter(|s| {
                let b0 = s.get("b0").unwrap_or(false);
                let b1 = s.get("b1").unwrap_or(false);
                let value = (b1 as u8) * 2 + (b0 as u8);
                let overflow = b0 && b1;
                format!("Counter = {} (binary: {}{}), overflow = {}", value, b1 as u8, b0 as u8, overflow)
            })
            .with_transition_interpreter(|from, to| {
                let from_b0 = from.get("b0").unwrap_or(false);
                let from_b1 = from.get("b1").unwrap_or(false);
                let to_b0 = to.get("b0").unwrap_or(false);
                let to_b1 = to.get("b1").unwrap_or(false);
                let from_val = (from_b1 as u8) * 2 + (from_b0 as u8);
                let to_val = (to_b1 as u8) * 2 + (to_b0 as u8);
                format!("Counter increments: {} → {}", from_val, to_val)
            })
            .build();

        println!("{}", explanation);

        // Also show trace with overflow label
        println!("\n── Trace with Labels ──────────────────────────────────────────────");
        let vis = cex.clone().with_annotations().visualize().with_label("overflow", |s| {
            let b0 = s.get("b0").unwrap_or(false);
            let b1 = s.get("b1").unwrap_or(false);
            b0 && b1
        });
        println!("{}", vis.render());
    }
}
