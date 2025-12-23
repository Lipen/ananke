//! Incremental safety verification.
//!
//! This module provides incremental safety checking for transition systems.
//! Given a safety property (invariant), it can efficiently re-verify when
//! the system or property changes.

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use crate::delta::{Delta, SystemDelta};
use crate::incremental_ts::IncrementalTransSystem;
use crate::metrics::MetricsCollector;
use crate::traits::{IncrementalTransitionSystem, IncrementalVerificationResult, IncrementalVerifier, VerificationResult};

/// Incremental safety checker.
///
/// Verifies that all reachable states satisfy an invariant property,
/// with support for incremental updates.
pub struct IncrementalSafetyChecker {
    /// The incremental transition system.
    ts: IncrementalTransSystem,
    /// The safety invariant: I(s) - states that satisfy the property.
    invariant: Ref,
    /// Cached verification result.
    result: Option<VerificationResult>,
    /// Cached violation states (if any).
    violation: Option<Ref>,
    /// Metrics collector.
    #[allow(dead_code)]
    metrics: MetricsCollector,
}

impl IncrementalSafetyChecker {
    /// Create a new safety checker.
    pub fn new(ts: IncrementalTransSystem, invariant: Ref) -> Self {
        IncrementalSafetyChecker {
            ts,
            invariant,
            result: None,
            violation: None,
            metrics: MetricsCollector::new(),
        }
    }

    /// Get the BDD manager.
    pub fn bdd(&self) -> &Bdd {
        self.ts.bdd()
    }

    /// Get the underlying transition system.
    pub fn ts(&self) -> &IncrementalTransSystem {
        &self.ts
    }

    /// Get mutable access to the transition system.
    pub fn ts_mut(&mut self) -> &mut IncrementalTransSystem {
        self.result = None;
        self.violation = None;
        &mut self.ts
    }

    /// Get the current invariant.
    pub fn invariant(&self) -> Ref {
        self.invariant
    }

    /// Set a new invariant.
    pub fn set_invariant(&mut self, invariant: Ref) {
        self.invariant = invariant;
        self.result = None;
        self.violation = None;
    }

    /// Check if all reachable states satisfy the invariant.
    ///
    /// Safety: Reach ⊆ Invariant
    fn check_safety(&mut self) -> VerificationResult {
        let reach = self.ts.reachable();
        let invariant = self.invariant;

        // Violation = Reach ∧ ¬Invariant
        let violation = self.bdd().apply_and(reach, -invariant);

        if self.bdd().is_zero(violation) {
            VerificationResult::Holds
        } else {
            self.violation = Some(violation);
            VerificationResult::Violated {
                violation_states: violation,
            }
        }
    }

    /// Incrementally update after transition changes.
    fn update_transitions(&mut self, delta: Delta) -> IncrementalVerificationResult {
        let prev_result = self.result.take();

        // Apply delta to transition system
        let effect = self.ts.update_transitions(delta.clone());

        match effect {
            crate::delta::DeltaEffect::NoChange => {
                // No change to reachability, result unchanged
                if let Some(r) = prev_result {
                    self.result = Some(r.clone());
                    if r.holds() {
                        return IncrementalVerificationResult::StillHolds;
                    } else {
                        return IncrementalVerificationResult::StillFails;
                    }
                }
            }
            crate::delta::DeltaEffect::LocalChange { .. } => {
                // Reachability changed, but we can check incrementally
                if delta.added.is_some() {
                    // New transitions: check if newly reachable states violate invariant
                    let reach = self.ts.reachable();
                    let invariant = self.invariant;
                    let new_violation = self.bdd().apply_and(reach, -invariant);

                    let was_safe = prev_result.as_ref().map(|r| r.holds()).unwrap_or(true);

                    if self.bdd().is_zero(new_violation) {
                        self.result = Some(VerificationResult::Holds);
                        self.violation = None;
                        if was_safe {
                            return IncrementalVerificationResult::StillHolds;
                        } else {
                            return IncrementalVerificationResult::NowHolds;
                        }
                    } else {
                        self.violation = Some(new_violation);
                        self.result = Some(VerificationResult::Violated {
                            violation_states: new_violation,
                        });
                        if was_safe {
                            return IncrementalVerificationResult::NowFails { new_violation };
                        } else {
                            return IncrementalVerificationResult::StillFails;
                        }
                    }
                }
            }
            crate::delta::DeltaEffect::GlobalRebuildRequired => {
                // Full recomputation needed
            }
        }

        // Fall back to full verification
        let result = self.check_safety();
        self.result = Some(result.clone());
        IncrementalVerificationResult::Recomputed(result)
    }

    /// Update the invariant and re-verify.
    fn update_invariant(&mut self, new_invariant: Ref) -> IncrementalVerificationResult {
        let old_invariant = self.invariant;
        let prev_result = self.result.take();

        self.invariant = new_invariant;

        // Check if invariant strengthened or weakened
        let strengthened = self.bdd().apply_and(old_invariant, -new_invariant);
        let weakened = self.bdd().apply_and(new_invariant, -old_invariant);

        let reach = self.ts.reachable();

        // If invariant only weakened and was safe, still safe
        if self.bdd().is_zero(strengthened) {
            if let Some(VerificationResult::Holds) = prev_result {
                self.result = Some(VerificationResult::Holds);
                return IncrementalVerificationResult::StillHolds;
            }
        }

        // If invariant only strengthened and was failing, check if still failing
        if self.bdd().is_zero(weakened) {
            if let Some(VerificationResult::Violated { violation_states }) = prev_result {
                // Previous violations might still exist
                let still_violating = self.bdd().apply_and(violation_states, -new_invariant);
                if !self.bdd().is_zero(still_violating) {
                    self.violation = Some(still_violating);
                    self.result = Some(VerificationResult::Violated {
                        violation_states: still_violating,
                    });
                    return IncrementalVerificationResult::StillFails;
                }
            }
        }

        // Full recheck
        let new_violation = self.bdd().apply_and(reach, -new_invariant);

        if self.bdd().is_zero(new_violation) {
            self.result = Some(VerificationResult::Holds);
            self.violation = None;
            let was_failing = prev_result.map(|r| !r.holds()).unwrap_or(false);
            if was_failing {
                IncrementalVerificationResult::NowHolds
            } else {
                IncrementalVerificationResult::StillHolds
            }
        } else {
            self.violation = Some(new_violation);
            self.result = Some(VerificationResult::Violated {
                violation_states: new_violation,
            });
            let was_safe = prev_result.map(|r| r.holds()).unwrap_or(true);
            if was_safe {
                IncrementalVerificationResult::NowFails { new_violation }
            } else {
                IncrementalVerificationResult::StillFails
            }
        }
    }
}

impl IncrementalVerifier for IncrementalSafetyChecker {
    fn verify(&mut self) -> VerificationResult {
        if let Some(ref result) = self.result {
            return result.clone();
        }

        let result = self.check_safety();
        self.result = Some(result.clone());
        result
    }

    fn update(&mut self, delta: SystemDelta) -> IncrementalVerificationResult {
        // Handle transition changes
        if let Some(trans_delta) = delta.transition_delta {
            return self.update_transitions(trans_delta);
        }

        // Handle property changes
        if let Some(prop_delta) = delta.property_delta {
            if let Some(new_inv) = prop_delta.added {
                // New invariant replaces old
                return self.update_invariant(new_inv);
            }
        }

        // Handle state changes (force full recompute)
        if let Some(_state_delta) = delta.state_delta {
            self.result = None;
            self.violation = None;
            let result = self.check_safety();
            self.result = Some(result.clone());
            return IncrementalVerificationResult::Recomputed(result);
        }

        // Empty delta
        if let Some(ref result) = self.result {
            if result.holds() {
                IncrementalVerificationResult::StillHolds
            } else {
                IncrementalVerificationResult::StillFails
            }
        } else {
            let result = self.check_safety();
            self.result = Some(result.clone());
            IncrementalVerificationResult::Recomputed(result)
        }
    }

    fn status(&self) -> &VerificationResult {
        self.result.as_ref().expect("verify() must be called before status()")
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use model_checking::transition::Var;

    use super::*;

    fn create_simple_system() -> (Rc<Bdd>, IncrementalTransSystem, Ref, Ref, Ref) {
        let bdd = Rc::new(Bdd::default());
        let mut ts = IncrementalTransSystem::new(bdd.clone());

        // Two-bit counter: 00 -> 01 -> 10 -> 11 -> 00
        let (b0, b0_next) = ts.declare_var(Var::new("b0"));
        let (b1, b1_next) = ts.declare_var(Var::new("b1"));

        let b0_ref = bdd.mk_var(b0);
        let b1_ref = bdd.mk_var(b1);
        let b0_next_ref = bdd.mk_var(b0_next);
        let b1_next_ref = bdd.mk_var(b1_next);

        // States
        let s00 = bdd.apply_and(-b0_ref, -b1_ref);
        let s01 = bdd.apply_and(b0_ref, -b1_ref);
        let s10 = bdd.apply_and(-b0_ref, b1_ref);
        let s11 = bdd.apply_and(b0_ref, b1_ref);

        let s00_next = bdd.apply_and(-b0_next_ref, -b1_next_ref);
        let s01_next = bdd.apply_and(b0_next_ref, -b1_next_ref);
        let s10_next = bdd.apply_and(-b0_next_ref, b1_next_ref);
        let s11_next = bdd.apply_and(b0_next_ref, b1_next_ref);

        // Initial: 00
        ts.set_initial(s00);

        // Transitions: 00->01, 01->10, 10->11, 11->00
        let t1 = bdd.apply_and(s00, s01_next);
        let t2 = bdd.apply_and(s01, s10_next);
        let t3 = bdd.apply_and(s10, s11_next);
        let t4 = bdd.apply_and(s11, s00_next);
        let trans = bdd.apply_or(bdd.apply_or(t1, t2), bdd.apply_or(t3, t4));
        ts.set_transition(trans);

        // Invariant: not state 11 (b0 ∧ b1)
        let safe_states = -s11;

        (bdd, ts, safe_states, s11, t3)
    }

    #[test]
    fn test_safety_holds_initially() {
        let (_bdd, ts, safe_states, _s11, _t3) = create_simple_system();

        // Initially only 00 is reachable from 00 with no transitions yet
        // But we set up all transitions, so all states are reachable

        let mut checker = IncrementalSafetyChecker::new(ts, safe_states);
        let result = checker.verify();

        // All states reachable, s11 violates invariant
        assert!(!result.holds());
    }

    #[test]
    fn test_strengthen_invariant() {
        let (bdd, ts, safe_states, _s11, _t3) = create_simple_system();

        let mut checker = IncrementalSafetyChecker::new(ts, bdd.one()); // Initially all safe
        let result = checker.verify();
        assert!(result.holds());

        // Strengthen: exclude s11
        let update_result = checker.update_invariant(safe_states);

        // Should now fail
        assert!(!update_result.holds());
    }
}
