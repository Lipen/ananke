//! Incremental traits for decision diagram operations.
//!
//! This module defines the trait hierarchy for incremental DD operations:
//!
//! - [`IncrementalObject`]: Base trait for delta-aware semantic objects
//! - [`IncrementalTransitionSystem`]: Transition systems with incremental updates
//! - [`IncrementalFixpoint`]: Fixpoint engines with partial recomputation
//! - [`IncrementalVerifier`]: Verifiers with incremental property checking
//! - [`IncrementalSynthesizer`]: Synthesizers with constraint addition/removal

use ananke_bdd::reference::Ref;

use crate::delta::{Delta, DeltaEffect, SystemDelta};

/// Base trait for semantic objects that support incremental updates.
///
/// Any DD-backed semantic object that can be modified via deltas should
/// implement this trait.
pub trait IncrementalObject {
    /// Apply a delta to this object and return the effect classification.
    ///
    /// The effect classification helps callers understand how much work
    /// was required and whether incremental update was possible.
    fn apply_delta(&mut self, delta: Delta) -> DeltaEffect;

    /// Get the current semantic content as a BDD reference.
    fn content(&self) -> Ref;

    /// Get the version number (incremented on each change).
    fn version(&self) -> u64;
}

/// Trait for transition systems that support incremental state/transition updates.
pub trait IncrementalTransitionSystem {
    /// Get the current set of states.
    fn states(&self) -> Ref;

    /// Get the current transition relation.
    fn transitions(&self) -> Ref;

    /// Get the initial states.
    fn initial(&self) -> Ref;

    /// Update the state space with a delta.
    ///
    /// Returns the effect on the overall system.
    fn update_states(&mut self, delta: Delta) -> DeltaEffect;

    /// Update the transition relation with a delta.
    ///
    /// Returns the effect on the overall system.
    fn update_transitions(&mut self, delta: Delta) -> DeltaEffect;

    /// Update the initial states with a delta.
    fn update_initial(&mut self, delta: Delta) -> DeltaEffect;
}

/// Result of an incremental fixpoint computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixpointUpdate {
    /// The fixpoint did not change.
    Unchanged,

    /// The fixpoint was partially recomputed.
    PartiallyRecomputed {
        /// Number of iterations performed.
        iterations: usize,
        /// Size of the frontier at termination.
        frontier_size: usize,
    },

    /// The fixpoint was fully recomputed from scratch.
    FullyRecomputed {
        /// Total number of iterations.
        total_iterations: usize,
    },
}

impl FixpointUpdate {
    /// Check if any recomputation occurred.
    pub fn changed(&self) -> bool {
        !matches!(self, FixpointUpdate::Unchanged)
    }

    /// Check if full recomputation was required.
    pub fn was_full_recompute(&self) -> bool {
        matches!(self, FixpointUpdate::FullyRecomputed { .. })
    }
}

/// Trait for fixpoint engines that support incremental recomputation.
pub trait IncrementalFixpoint {
    /// Compute the fixpoint from scratch.
    fn compute(&mut self) -> Ref;

    /// Get the current fixpoint value.
    fn current(&self) -> Ref;

    /// Apply a delta and incrementally update the fixpoint.
    fn apply_delta(&mut self, delta: Delta) -> FixpointUpdate;

    /// Check if the fixpoint is currently valid.
    fn is_valid(&self) -> bool;

    /// Force a full recomputation.
    fn recompute(&mut self) -> FixpointUpdate;
}

/// Result of a verification check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationResult {
    /// The property holds.
    Holds,

    /// The property is violated.
    Violated {
        /// States where the violation occurs.
        violation_states: Ref,
    },
}

impl VerificationResult {
    /// Check if the property holds.
    pub fn holds(&self) -> bool {
        matches!(self, VerificationResult::Holds)
    }

    /// Get the violation states if any.
    pub fn violation(&self) -> Option<Ref> {
        match self {
            VerificationResult::Violated { violation_states } => Some(*violation_states),
            VerificationResult::Holds => None,
        }
    }
}

/// Result of an incremental verification update.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncrementalVerificationResult {
    /// The property still holds (was holding before and still holds).
    StillHolds,

    /// The property still fails (was failing before and still fails).
    StillFails,

    /// The property now holds (was failing before, now holds).
    NowHolds,

    /// The property now fails (was holding before, now fails).
    NowFails {
        /// New violation states.
        new_violation: Ref,
    },

    /// Full recomputation was required.
    Recomputed(VerificationResult),
}

impl IncrementalVerificationResult {
    /// Check if the property currently holds.
    pub fn holds(&self) -> bool {
        matches!(
            self,
            IncrementalVerificationResult::StillHolds
                | IncrementalVerificationResult::NowHolds
                | IncrementalVerificationResult::Recomputed(VerificationResult::Holds)
        )
    }

    /// Check if this was an incremental update (not full recompute).
    pub fn was_incremental(&self) -> bool {
        !matches!(self, IncrementalVerificationResult::Recomputed(_))
    }
}

/// Trait for verifiers that support incremental property checking.
pub trait IncrementalVerifier {
    /// Perform full verification.
    fn verify(&mut self) -> VerificationResult;

    /// Update the system and incrementally re-verify.
    fn update(&mut self, delta: SystemDelta) -> IncrementalVerificationResult;

    /// Get the current verification status.
    fn status(&self) -> &VerificationResult;
}

/// Result of adding/removing a constraint in synthesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintEffect {
    /// The constraint had no effect (already implied or contradicted).
    NoEffect,

    /// The solution space was reduced.
    Shrunk {
        /// Estimate of removed nodes (BDD size decrease).
        removed_nodes: u64,
    },

    /// The solution space became empty (unsatisfiable).
    Unsat,
}

impl ConstraintEffect {
    /// Check if the constraint caused UNSAT.
    pub fn is_unsat(&self) -> bool {
        matches!(self, ConstraintEffect::Unsat)
    }

    /// Check if the constraint had any effect.
    pub fn had_effect(&self) -> bool {
        !matches!(self, ConstraintEffect::NoEffect)
    }
}

/// Trait for synthesizers that support incremental constraint management.
pub trait IncrementalSynthesizer {
    /// Get the current solution space.
    fn solution_space(&self) -> Ref;

    /// Add a constraint to the solution space.
    fn add_constraint(&mut self, constraint: Ref) -> ConstraintEffect;

    /// Remove a previously added constraint (if supported).
    ///
    /// Returns `None` if constraint removal is not supported.
    fn remove_constraint(&mut self, constraint_id: usize) -> Option<ConstraintEffect>;

    /// Check if the current solution space is satisfiable.
    fn is_sat(&self) -> bool;

    /// Get the number of active constraints.
    fn constraint_count(&self) -> usize;
}

/// Trait for objects that can report incremental metrics.
pub trait IncrementalMetrics {
    /// Get the number of nodes reused in the last operation.
    fn nodes_reused(&self) -> u64;

    /// Get the number of nodes rebuilt in the last operation.
    fn nodes_rebuilt(&self) -> u64;

    /// Get the reuse ratio (reused / total).
    fn reuse_ratio(&self) -> f64 {
        let reused = self.nodes_reused();
        let rebuilt = self.nodes_rebuilt();
        let total = reused + rebuilt;
        if total == 0 {
            1.0
        } else {
            reused as f64 / total as f64
        }
    }

    /// Get the number of iterations saved compared to full recompute.
    fn iterations_saved(&self) -> usize;
}
