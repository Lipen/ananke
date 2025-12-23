//! Incremental constraint-based synthesis.
//!
//! This module provides an incremental synthesizer that maintains a solution
//! space under constraint addition and removal.

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use ananke_bdd::types::Var;

use crate::metrics::{IncrementalMetricsData, MetricsCollector};
use crate::traits::{ConstraintEffect, IncrementalSynthesizer};

/// An incremental constraint-based synthesizer.
///
/// Maintains a solution space (represented as a BDD) that shrinks
/// as constraints are added. Supports:
/// - Efficient constraint addition with effect classification
/// - UNSAT detection
/// - Optional constraint removal (with overhead)
pub struct IncrementalConstraintSynthesizer {
    /// BDD manager.
    bdd: Rc<Bdd>,
    /// Current solution space.
    solution_space: Ref,
    /// Variables in the solution space.
    variables: Vec<Var>,
    /// History of constraints (for removal support).
    constraints: Vec<ConstraintInfo>,
    /// Metrics collector.
    metrics: MetricsCollector,
}

/// Information about an added constraint.
#[derive(Debug, Clone)]
struct ConstraintInfo {
    /// The constraint BDD.
    constraint: Ref,
    /// Size of solution space before adding this constraint.
    #[allow(dead_code)]
    space_before: u64,
    /// Whether this constraint is currently active.
    active: bool,
}

impl IncrementalConstraintSynthesizer {
    /// Create a new synthesizer with the given variables.
    ///
    /// The initial solution space is the set of all assignments to the variables.
    pub fn new(bdd: Rc<Bdd>, variables: Vec<Var>) -> Self {
        let one = bdd.one();
        Self::with_initial_space(bdd, variables, one)
    }

    /// Create a synthesizer with a custom initial solution space.
    pub fn with_initial_space(bdd: Rc<Bdd>, variables: Vec<Var>, initial: Ref) -> Self {
        IncrementalConstraintSynthesizer {
            bdd,
            solution_space: initial,
            variables,
            constraints: Vec::new(),
            metrics: MetricsCollector::new(),
        }
    }

    /// Get the BDD manager.
    pub fn bdd(&self) -> &Bdd {
        &self.bdd
    }

    /// Get the current solution count (may overflow for large spaces).
    pub fn solution_count(&self) -> Option<u64> {
        use num_traits::ToPrimitive;
        let count = self.bdd.sat_count(self.solution_space, self.variables.len());
        count.to_u64()
    }

    /// Get the size of the solution space BDD.
    pub fn space_size(&self) -> u64 {
        self.bdd.size(self.solution_space)
    }

    /// Get any satisfying assignment if the space is non-empty.
    pub fn get_solution(&self) -> Option<Vec<(Var, bool)>> {
        if self.bdd.is_zero(self.solution_space) {
            return None;
        }

        // Use SAT enumeration to get one solution
        let lits = self.bdd.one_sat(self.solution_space)?;

        Some(
            lits.into_iter()
                .map(|lit| (lit.var(), lit.is_positive()))
                .filter(|(v, _)| self.variables.contains(v))
                .collect(),
        )
    }

    /// Add multiple constraints at once (more efficient than one at a time).
    pub fn add_constraints(&mut self, constraints: &[Ref]) -> Vec<ConstraintEffect> {
        constraints.iter().map(|c| self.add_constraint(*c)).collect()
    }

    /// Check if a constraint would cause UNSAT without actually adding it.
    pub fn would_cause_unsat(&self, constraint: Ref) -> bool {
        let potential = self.bdd.apply_and(self.solution_space, constraint);
        self.bdd.is_zero(potential)
    }

    /// Get the number of variables.
    pub fn num_variables(&self) -> usize {
        self.variables.len()
    }

    /// Get the variables.
    pub fn variables(&self) -> &[Var] {
        &self.variables
    }

    /// Reset to initial state (all solutions valid).
    pub fn reset(&mut self) {
        self.solution_space = self.bdd.one();
        self.constraints.clear();
    }

    /// Get metrics.
    pub fn metrics(&self) -> &IncrementalMetricsData {
        self.metrics.metrics()
    }
}

impl IncrementalSynthesizer for IncrementalConstraintSynthesizer {
    fn solution_space(&self) -> Ref {
        self.solution_space
    }

    fn add_constraint(&mut self, constraint: Ref) -> ConstraintEffect {
        let old_space = self.solution_space;
        let old_size = self.bdd.size(old_space);

        // Apply constraint: new_space = old_space ∧ constraint
        let new_space = self.bdd.apply_and(old_space, constraint);

        // Check for UNSAT
        if self.bdd.is_zero(new_space) {
            self.solution_space = new_space; // Set to zero/UNSAT
            self.metrics.record_global_rebuild();
            return ConstraintEffect::Unsat;
        }

        // Check for no effect (constraint was already implied)
        if new_space == old_space {
            self.metrics.record_no_change();
            return ConstraintEffect::NoEffect;
        }

        // Record constraint info for potential removal
        self.constraints.push(ConstraintInfo {
            constraint,
            space_before: old_size,
            active: true,
        });

        // Update solution space
        self.solution_space = new_space;

        let new_size = self.bdd.size(new_space);
        let removed = old_size.saturating_sub(new_size);

        self.metrics.record_local_change();

        ConstraintEffect::Shrunk { removed_nodes: removed }
    }

    fn remove_constraint(&mut self, constraint_id: usize) -> Option<ConstraintEffect> {
        if constraint_id >= self.constraints.len() {
            return None;
        }

        if !self.constraints[constraint_id].active {
            return Some(ConstraintEffect::NoEffect);
        }

        // Mark as inactive
        self.constraints[constraint_id].active = false;

        // Recompute solution space from scratch with remaining constraints
        // (This is the naive approach; could be optimized with incremental algorithms)
        let mut new_space = self.bdd.one();
        for info in &self.constraints {
            if info.active {
                new_space = self.bdd.apply_and(new_space, info.constraint);
            }
        }

        let old_size = self.bdd.size(self.solution_space);
        let new_size = self.bdd.size(new_space);

        self.solution_space = new_space;

        if new_size > old_size {
            Some(ConstraintEffect::Shrunk {
                removed_nodes: new_size - old_size, // Actually grew
            })
        } else {
            Some(ConstraintEffect::NoEffect)
        }
    }

    fn is_sat(&self) -> bool {
        !self.bdd.is_zero(self.solution_space)
    }

    fn constraint_count(&self) -> usize {
        self.constraints.iter().filter(|c| c.active).count()
    }
}

/// Builder for creating a synthesizer with domain constraints.
pub struct SynthesizerBuilder {
    bdd: Rc<Bdd>,
    variables: Vec<Var>,
    domain_constraints: Vec<Ref>,
}

impl SynthesizerBuilder {
    /// Create a new builder.
    pub fn new(bdd: Rc<Bdd>) -> Self {
        SynthesizerBuilder {
            bdd,
            variables: Vec::new(),
            domain_constraints: Vec::new(),
        }
    }

    /// Add a variable.
    pub fn add_variable(mut self, var: Var) -> Self {
        self.variables.push(var);
        self
    }

    /// Add multiple variables.
    pub fn add_variables(mut self, vars: impl IntoIterator<Item = Var>) -> Self {
        self.variables.extend(vars);
        self
    }

    /// Add a domain constraint (applied before user constraints).
    pub fn add_domain_constraint(mut self, constraint: Ref) -> Self {
        self.domain_constraints.push(constraint);
        self
    }

    /// Build the synthesizer.
    pub fn build(self) -> IncrementalConstraintSynthesizer {
        let mut initial = self.bdd.one();
        for c in &self.domain_constraints {
            initial = self.bdd.apply_and(initial, *c);
        }

        IncrementalConstraintSynthesizer::with_initial_space(self.bdd, self.variables, initial)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_synthesis() {
        let bdd = Rc::new(Bdd::default());
        let vars = vec![Var::new(1), Var::new(2), Var::new(3)];

        let mut synth = IncrementalConstraintSynthesizer::new(bdd.clone(), vars);

        // Initially all solutions valid
        assert!(synth.is_sat());
        assert_eq!(synth.solution_count(), Some(8)); // 2^3

        // Add constraint: x1 = true
        let x1 = bdd.mk_var(Var::new(1));
        let effect = synth.add_constraint(x1);

        assert!(matches!(effect, ConstraintEffect::Shrunk { .. }));
        assert_eq!(synth.solution_count(), Some(4)); // x1=true, 2^2 for others

        // Add constraint: x2 = true
        let x2 = bdd.mk_var(Var::new(2));
        let effect = synth.add_constraint(x2);

        assert!(matches!(effect, ConstraintEffect::Shrunk { .. }));
        assert_eq!(synth.solution_count(), Some(2)); // x1=x2=true, 2^1 for x3
    }

    #[test]
    fn test_unsat_detection() {
        let bdd = Rc::new(Bdd::default());
        let vars = vec![Var::new(1)];

        let mut synth = IncrementalConstraintSynthesizer::new(bdd.clone(), vars);

        let x = bdd.mk_var(Var::new(1));

        // Add x = true
        synth.add_constraint(x);
        assert!(synth.is_sat());

        // Add x = false (contradiction)
        let effect = synth.add_constraint(-x);
        assert!(matches!(effect, ConstraintEffect::Unsat));
        assert!(!synth.is_sat());
    }

    #[test]
    fn test_implied_constraint() {
        let bdd = Rc::new(Bdd::default());
        let vars = vec![Var::new(1), Var::new(2)];

        let mut synth = IncrementalConstraintSynthesizer::new(bdd.clone(), vars);

        let x = bdd.mk_var(Var::new(1));
        let y = bdd.mk_var(Var::new(2));

        // Add x = true
        synth.add_constraint(x);

        // Add x ∨ y (implied by x = true)
        let x_or_y = bdd.apply_or(x, y);
        let effect = synth.add_constraint(x_or_y);

        assert!(matches!(effect, ConstraintEffect::NoEffect));
    }

    #[test]
    fn test_would_cause_unsat() {
        let bdd = Rc::new(Bdd::default());
        let vars = vec![Var::new(1)];

        let mut synth = IncrementalConstraintSynthesizer::new(bdd.clone(), vars);

        let x = bdd.mk_var(Var::new(1));

        synth.add_constraint(x);

        // Check without adding
        assert!(synth.would_cause_unsat(-x));
        assert!(!synth.would_cause_unsat(x)); // Already satisfied
    }
}
