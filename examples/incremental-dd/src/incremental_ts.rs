//! Incremental transition system implementation.
//!
//! This module wraps the model-checking `TransitionSystem` with incremental
//! update capabilities, tracking reachability state across modifications.

use std::rc::Rc;
use std::time::Instant;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use ananke_bdd::types::Var as BddVar;
use model_checking::transition::{TransitionSystem, Var};

use crate::delta::{Delta, DeltaEffect};
use crate::metrics::{IncrementalMetricsData, MetricsCollector};
use crate::traits::{FixpointUpdate, IncrementalFixpoint, IncrementalTransitionSystem};

/// An incremental transition system that tracks reachability state.
pub struct IncrementalTransSystem {
    /// The underlying transition system.
    ts: TransitionSystem,
    /// Current reachable states (cached).
    reach: Option<Ref>,
    /// Current frontier for incremental forward reachability.
    frontier: Option<Ref>,
    /// Version counter for cache invalidation.
    version: u64,
    /// Metrics collector.
    metrics: MetricsCollector,
}

impl IncrementalTransSystem {
    /// Create a new incremental transition system.
    pub fn new(bdd: Rc<Bdd>) -> Self {
        let ts = TransitionSystem::new(bdd);
        Self::from_ts(ts)
    }

    /// Create from an existing transition system.
    pub fn from_ts(ts: TransitionSystem) -> Self {
        IncrementalTransSystem {
            ts,
            reach: None,
            frontier: None,
            version: 0,
            metrics: MetricsCollector::new(),
        }
    }

    /// Get the underlying transition system.
    pub fn ts(&self) -> &TransitionSystem {
        &self.ts
    }

    /// Get mutable access to the underlying transition system.
    pub fn ts_mut(&mut self) -> &mut TransitionSystem {
        // Invalidate caches when mutating
        self.invalidate();
        &mut self.ts
    }

    /// Get the BDD manager.
    pub fn bdd(&self) -> &Bdd {
        self.ts.bdd()
    }

    /// Invalidate cached reachability data.
    fn invalidate(&mut self) {
        self.reach = None;
        self.frontier = None;
        self.version += 1;
    }

    /// Get the current version.
    pub fn version(&self) -> u64 {
        self.version
    }

    /// Declare a variable in the transition system.
    pub fn declare_var(&mut self, var: Var) -> (BddVar, BddVar) {
        self.ts_mut().declare_var(var)
    }

    /// Set the initial states.
    pub fn set_initial(&mut self, initial: Ref) {
        self.ts_mut().set_initial(initial);
    }

    /// Set the transition relation.
    pub fn set_transition(&mut self, transition: Ref) {
        self.ts_mut().set_transition(transition);
    }

    /// Compute reachable states (with caching).
    pub fn reachable(&mut self) -> Ref {
        if let Some(reach) = self.reach {
            return reach;
        }

        // Full recomputation
        let reach = self.compute_reachable_full();
        self.reach = Some(reach);
        reach
    }

    /// Full reachability computation.
    fn compute_reachable_full(&mut self) -> Ref {
        log::debug!("REACHABILITY: Starting full reachability computation");
        let start = Instant::now();
        let mut iterations = 0;
        let mut reached = self.ts.initial();
        let mut frontier = reached;

        loop {
            let new_states = self.ts.image(frontier);
            let new_reached = self.bdd().apply_or(reached, new_states);

            iterations += 1;

            if new_reached == reached {
                self.frontier = Some(self.bdd().zero());
                let duration = start.elapsed();
                self.metrics.record_full_recompute(duration, iterations);
                log::info!(
                    "REACHABILITY: Full computation completed in {:?} ({} iterations)",
                    duration,
                    iterations
                );
                return reached;
            }

            // New frontier = newly discovered states
            frontier = self.bdd().apply_and(new_states, -reached);
            reached = new_reached;
        }
    }

    /// Add transitions incrementally.
    ///
    /// When transitions are added, we need to propagate forward from
    /// states that gain new outgoing edges.
    pub fn add_transitions(&mut self, added: Ref) -> DeltaEffect {
        log::debug!("TRANSITIONS: Adding new transitions");
        let start = Instant::now();
        // First, update the transition relation
        let old_trans = self.ts.transition();
        let new_trans = self.ts.bdd().apply_or(old_trans, added);
        self.ts.set_transition(new_trans);
        self.version += 1;

        // Check if reachability is affected
        if self.reach.is_none() {
            log::debug!("TRANSITIONS: No cached reachability, skipping propagation");
            self.metrics.record_local_change();
            return DeltaEffect::LocalChange { affected_nodes: 0 };
        }

        let reach = self.reach.unwrap();

        // Find states with new outgoing edges that are currently reachable
        // These are: ∃s'. added(s, s') where s ∈ reach
        // We need to quantify out the NEXT-state vars to get source states
        let next_vars = self.ts.var_manager().next_vars();
        let states_with_new_edges = self.ts.bdd().exists(added, next_vars);

        // If no reachable state has new edges, reachability unchanged
        let affected_reachable = self.ts.bdd().apply_and(reach, states_with_new_edges);
        if self.ts.bdd().is_zero(affected_reachable) {
            log::debug!("TRANSITIONS: New transitions don't affect reachable states");
            self.metrics.record_no_change();
            return DeltaEffect::NoChange;
        }

        // Compute newly reachable states via the added transitions
        // Forward propagate from affected states
        let new_frontier = self.ts.image(affected_reachable);
        let truly_new = self.ts.bdd().apply_and(new_frontier, -reach);

        if self.ts.bdd().is_zero(truly_new) {
            log::debug!("TRANSITIONS: No new reachable states discovered");
            self.metrics.record_no_change();
            return DeltaEffect::NoChange;
        }

        // Incrementally extend reachability
        log::debug!("TRANSITIONS: Propagating forward from affected states");
        let (new_reach, iterations) = self.extend_reachability(reach, truly_new);
        self.reach = Some(new_reach);
        self.frontier = Some(self.bdd().zero());

        let affected = self.ts.bdd().size(truly_new) as usize;
        let duration = start.elapsed();
        self.metrics.record_local_change();
        self.metrics.record_incremental(duration, iterations);

        log::info!(
            "TRANSITIONS: Incremental propagation completed in {:?} ({} iterations, {} new nodes)",
            duration,
            iterations,
            affected
        );

        DeltaEffect::LocalChange { affected_nodes: affected }
    }

    /// Remove transitions incrementally.
    ///
    /// When transitions are removed, some states may become unreachable.
    /// This is harder to handle incrementally.
    pub fn remove_transitions(&mut self, removed: Ref) -> DeltaEffect {
        log::debug!("TRANSITIONS: Removing transitions");
        // First, update the transition relation
        let old_trans = self.ts.transition();
        let new_trans = self.ts.bdd().apply_and(old_trans, -removed);
        self.ts.set_transition(new_trans);
        self.version += 1;

        // If we don't have cached reachability, nothing to invalidate
        if self.reach.is_none() {
            log::debug!("TRANSITIONS: No cached reachability, skipping analysis");
            self.metrics.record_local_change();
            return DeltaEffect::LocalChange { affected_nodes: 0 };
        }

        let reach = self.reach.unwrap();
        let initial = self.ts.initial();

        // Find states that lost incoming edges
        // These are: ∃s. removed(s, s') where s' ∈ reach and s' ∉ initial
        let next_vars = self.ts.var_manager().next_vars();
        let states_losing_incoming = self.ts.bdd().exists(removed, next_vars);

        // Non-initial reachable states that lost incoming edges
        let at_risk = self
            .ts
            .bdd()
            .apply_and(states_losing_incoming, self.ts.bdd().apply_and(reach, -initial));

        if self.ts.bdd().is_zero(at_risk) {
            // No reachable non-initial state lost incoming edges
            log::debug!("TRANSITIONS: Removed transitions don't affect reachability");
            self.metrics.record_no_change();
            return DeltaEffect::NoChange;
        }

        // Conservative approach: recompute reachability
        // (Full incremental removal is more complex and may not be worth it)
        log::info!("TRANSITIONS: Transition removal requires global reachability rebuild");
        self.reach = None;
        self.frontier = None;
        self.metrics.record_global_rebuild();

        DeltaEffect::GlobalRebuildRequired
    }

    /// Extend reachability from current reach set with new frontier.
    fn extend_reachability(&self, mut reach: Ref, mut frontier: Ref) -> (Ref, usize) {
        let bdd = self.bdd();
        let mut iterations = 0;

        // First, add the frontier itself to reach (these are the newly discovered states)
        reach = bdd.apply_or(reach, frontier);

        while !bdd.is_zero(frontier) {
            let new_states = self.ts.image(frontier);
            let truly_new = bdd.apply_and(new_states, -reach);

            reach = bdd.apply_or(reach, truly_new);
            frontier = truly_new;
            iterations += 1;
        }

        (reach, iterations)
    }

    /// Get collected metrics.
    pub fn metrics(&self) -> &IncrementalMetricsData {
        self.metrics.metrics()
    }

    /// Reset metrics.
    pub fn reset_metrics(&mut self) {
        self.metrics = MetricsCollector::new();
    }
}

impl IncrementalTransitionSystem for IncrementalTransSystem {
    fn states(&self) -> Ref {
        self.bdd().one() // All states (implicit)
    }

    fn transitions(&self) -> Ref {
        self.ts.transition()
    }

    fn initial(&self) -> Ref {
        self.ts.initial()
    }

    fn update_states(&mut self, _delta: Delta) -> DeltaEffect {
        // State space changes are less common; force full recompute
        self.invalidate();
        DeltaEffect::GlobalRebuildRequired
    }

    fn update_transitions(&mut self, delta: Delta) -> DeltaEffect {
        // Handle additions first, then removals
        let mut effect = DeltaEffect::NoChange;

        if let Some(added) = delta.added {
            effect = self.add_transitions(added);
        }

        if let Some(removed) = delta.removed {
            let remove_effect = self.remove_transitions(removed);
            // Removal dominates (may require rebuild)
            if matches!(remove_effect, DeltaEffect::GlobalRebuildRequired) {
                effect = remove_effect;
            }
        }

        effect
    }

    fn update_initial(&mut self, delta: Delta) -> DeltaEffect {
        let old_initial = self.ts.initial();
        let new_initial = delta.apply(self.bdd(), old_initial);

        self.ts.set_initial(new_initial);

        // Initial state changes require recomputation
        if let Some(added) = delta.added {
            if !self.bdd().is_zero(added) {
                // New initial states: extend reachability
                if let Some(reach) = self.reach {
                    let truly_new = self.bdd().apply_and(added, -reach);
                    if !self.bdd().is_zero(truly_new) {
                        let (new_reach, _) = self.extend_reachability(reach, truly_new);
                        self.reach = Some(new_reach);
                        return DeltaEffect::LocalChange { affected_nodes: 1 };
                    }
                }
            }
        }

        if delta.removed.is_some() {
            // Removing initial states may shrink reachability
            self.invalidate();
            return DeltaEffect::GlobalRebuildRequired;
        }

        DeltaEffect::NoChange
    }
}

/// Incremental reachability fixpoint engine.
///
/// Maintains a reachability fixpoint that can be incrementally updated
/// when the transition system changes.
pub struct IncrementalReachabilityFixpoint {
    /// The underlying transition system.
    ts: IncrementalTransSystem,
    /// Current fixpoint (reachable states).
    current: Ref,
    /// Current frontier (states to explore next).
    frontier: Ref,
    /// Number of iterations performed in last computation.
    iterations: usize,
    /// Whether the fixpoint is complete and valid.
    is_valid: bool,
    /// Metrics collector.
    metrics: MetricsCollector,
}

impl IncrementalReachabilityFixpoint {
    /// Create a new fixpoint engine wrapping a transition system.
    pub fn new(ts: IncrementalTransSystem) -> Self {
        let bdd = ts.bdd();
        let zero = bdd.zero();
        IncrementalReachabilityFixpoint {
            ts,
            current: zero,
            frontier: zero,
            iterations: 0,
            is_valid: false,
            metrics: MetricsCollector::new(),
        }
    }

    /// Create from an existing transition system with initial computation.
    pub fn with_initial_compute(mut ts: IncrementalTransSystem) -> Self {
        let current = ts.reachable();
        let zero = ts.bdd().zero();
        IncrementalReachabilityFixpoint {
            ts,
            current,
            frontier: zero,
            iterations: 0,
            is_valid: true,
            metrics: MetricsCollector::new(),
        }
    }

    /// Get the underlying transition system.
    pub fn ts(&self) -> &IncrementalTransSystem {
        &self.ts
    }

    /// Get mutable access to the transition system.
    ///
    /// This invalidates the fixpoint.
    pub fn ts_mut(&mut self) -> &mut IncrementalTransSystem {
        self.is_valid = false;
        &mut self.ts
    }

    /// Get the BDD manager.
    pub fn bdd(&self) -> &Bdd {
        self.ts.bdd()
    }

    /// Add transitions and incrementally update the fixpoint.
    pub fn add_transitions(&mut self, added: Ref) -> FixpointUpdate {
        use crate::traits::FixpointUpdate;

        if !self.is_valid {
            // Need full recomputation first
            self.compute();
            return FixpointUpdate::FullyRecomputed {
                total_iterations: self.iterations,
            };
        }

        let effect = self.ts.add_transitions(added);

        match effect {
            DeltaEffect::NoChange => FixpointUpdate::Unchanged,
            DeltaEffect::LocalChange { affected_nodes } => {
                // The transition system already updated reach
                self.current = self.ts.reachable();
                self.metrics.record_local_change();
                FixpointUpdate::PartiallyRecomputed {
                    iterations: 1,
                    frontier_size: affected_nodes,
                }
            }
            DeltaEffect::GlobalRebuildRequired => {
                self.is_valid = false;
                self.compute();
                FixpointUpdate::FullyRecomputed {
                    total_iterations: self.iterations,
                }
            }
        }
    }

    /// Remove transitions and update the fixpoint.
    pub fn remove_transitions(&mut self, removed: Ref) -> FixpointUpdate {
        use crate::traits::FixpointUpdate;

        if !self.is_valid {
            self.compute();
            return FixpointUpdate::FullyRecomputed {
                total_iterations: self.iterations,
            };
        }

        let effect = self.ts.remove_transitions(removed);

        match effect {
            DeltaEffect::NoChange => FixpointUpdate::Unchanged,
            DeltaEffect::LocalChange { .. } => {
                self.current = self.ts.reachable();
                self.metrics.record_local_change();
                FixpointUpdate::PartiallyRecomputed {
                    iterations: 1,
                    frontier_size: 0,
                }
            }
            DeltaEffect::GlobalRebuildRequired => {
                self.is_valid = false;
                self.compute();
                FixpointUpdate::FullyRecomputed {
                    total_iterations: self.iterations,
                }
            }
        }
    }

    /// Get the metrics.
    pub fn metrics(&self) -> &IncrementalMetricsData {
        self.metrics.metrics()
    }
}

impl IncrementalFixpoint for IncrementalReachabilityFixpoint {
    fn compute(&mut self) -> Ref {
        log::debug!("FIXPOINT: Starting fixpoint computation");
        let start = Instant::now();
        let bdd = self.ts.bdd();
        let mut reached = self.ts.ts().initial();
        let mut frontier = reached;
        let mut iterations = 0;

        loop {
            let new_states = self.ts.ts().image(frontier);
            let new_reached = bdd.apply_or(reached, new_states);

            iterations += 1;

            if new_reached == reached {
                self.current = reached;
                self.frontier = bdd.zero();
                self.iterations = iterations;
                self.is_valid = true;
                let duration = start.elapsed();
                self.metrics.record_full_recompute(duration, iterations);
                log::info!("FIXPOINT: Fixpoint reached in {:?} ({} iterations)", duration, iterations);
                return reached;
            }

            frontier = bdd.apply_and(new_states, -reached);
            reached = new_reached;
        }
    }

    fn current(&self) -> Ref {
        self.current
    }

    fn apply_delta(&mut self, delta: Delta) -> FixpointUpdate {
        log::debug!("FIXPOINT: Applying delta");
        // Handle transition changes
        let effect = self.ts.update_transitions(delta);

        match effect {
            DeltaEffect::NoChange => {
                log::debug!("FIXPOINT: Delta had no effect on fixpoint");
                FixpointUpdate::Unchanged
            }
            DeltaEffect::LocalChange { affected_nodes } => {
                log::debug!("FIXPOINT: Local change detected, {} affected nodes", affected_nodes);
                self.current = self.ts.reachable();
                FixpointUpdate::PartiallyRecomputed {
                    iterations: 1,
                    frontier_size: affected_nodes,
                }
            }
            DeltaEffect::GlobalRebuildRequired => {
                log::info!("FIXPOINT: Global rebuild required");
                self.is_valid = false;
                self.compute();
                FixpointUpdate::FullyRecomputed {
                    total_iterations: self.iterations,
                }
            }
        }
    }

    fn is_valid(&self) -> bool {
        self.is_valid
    }

    fn recompute(&mut self) -> FixpointUpdate {
        self.is_valid = false;
        self.compute();
        FixpointUpdate::FullyRecomputed {
            total_iterations: self.iterations,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::IncrementalFixpoint;

    #[test]
    fn test_basic_reachability() {
        let bdd = Rc::new(Bdd::default());
        let mut ts = IncrementalTransSystem::new(bdd.clone());

        // Create a simple 2-state system: s0 -> s1
        let (s_pres, s_next) = ts.declare_var(Var::new("s"));

        let s0 = -bdd.mk_var(s_pres);
        let s1 = bdd.mk_var(s_pres);
        let _s0_next = -bdd.mk_var(s_next);
        let s1_next = bdd.mk_var(s_next);

        // Initial: s0
        ts.set_initial(s0);

        // Transition: s0 -> s1
        let trans = bdd.apply_and(s0, s1_next);
        ts.set_transition(trans);

        // Reachable should be {s0, s1}
        let reach = ts.reachable();
        assert!(!bdd.is_zero(bdd.apply_and(reach, s0)));
        assert!(!bdd.is_zero(bdd.apply_and(reach, s1)));
    }

    #[test]
    fn test_add_transitions() {
        let bdd = Rc::new(Bdd::default());
        let mut ts = IncrementalTransSystem::new(bdd.clone());

        // Create a 3-state system
        let (s0_var, s0_next) = ts.declare_var(Var::new("s0"));
        let (s1_var, s1_next) = ts.declare_var(Var::new("s1"));

        let s00 = bdd.apply_and(-bdd.mk_var(s0_var), -bdd.mk_var(s1_var));
        let s01 = bdd.apply_and(-bdd.mk_var(s0_var), bdd.mk_var(s1_var));
        let s10 = bdd.apply_and(bdd.mk_var(s0_var), -bdd.mk_var(s1_var));

        // Initial: state 00
        ts.set_initial(s00);

        // Transition: 00 -> 01
        let s01_next_enc = bdd.apply_and(-bdd.mk_var(s0_next), bdd.mk_var(s1_next));
        let trans1 = bdd.apply_and(s00, s01_next_enc);
        ts.set_transition(trans1);

        // Compute initial reachability
        let _reach1 = ts.reachable();

        // Add transition: 01 -> 10
        let s10_next_enc = bdd.apply_and(bdd.mk_var(s0_next), -bdd.mk_var(s1_next));
        let trans2 = bdd.apply_and(s01, s10_next_enc);
        let effect = ts.add_transitions(trans2);

        // Should be a local change
        assert!(
            matches!(effect, DeltaEffect::LocalChange { .. }),
            "Expected LocalChange, got {:?}",
            effect
        );

        // New reachability should include s10
        let reach2 = ts.reachable();
        assert!(!bdd.is_zero(bdd.apply_and(reach2, s10)));
    }

    #[test]
    fn test_fixpoint_compute() {
        let bdd = Rc::new(Bdd::default());
        let mut ts = IncrementalTransSystem::new(bdd.clone());

        // Create a chain: s0 -> s1 -> s2
        let (s0_var, s0_next) = ts.declare_var(Var::new("b0"));
        let (s1_var, s1_next) = ts.declare_var(Var::new("b1"));

        // States: 00, 01, 10
        let s00 = bdd.apply_and(-bdd.mk_var(s0_var), -bdd.mk_var(s1_var));
        let s01 = bdd.apply_and(-bdd.mk_var(s0_var), bdd.mk_var(s1_var));
        let s10 = bdd.apply_and(bdd.mk_var(s0_var), -bdd.mk_var(s1_var));

        // Encodings for next states
        let s01_next = bdd.apply_and(-bdd.mk_var(s0_next), bdd.mk_var(s1_next));
        let s10_next = bdd.apply_and(bdd.mk_var(s0_next), -bdd.mk_var(s1_next));

        ts.set_initial(s00);

        // Transitions: 00 -> 01, 01 -> 10
        let t1 = bdd.apply_and(s00, s01_next);
        let t2 = bdd.apply_and(s01, s10_next);
        let trans = bdd.apply_or(t1, t2);
        ts.set_transition(trans);

        // Create fixpoint engine
        let mut fp = IncrementalReachabilityFixpoint::new(ts);
        assert!(!fp.is_valid());

        // Compute fixpoint
        let reach = fp.compute();
        assert!(fp.is_valid());

        // Should reach all three states
        assert!(!bdd.is_zero(bdd.apply_and(reach, s00)));
        assert!(!bdd.is_zero(bdd.apply_and(reach, s01)));
        assert!(!bdd.is_zero(bdd.apply_and(reach, s10)));
    }

    #[test]
    fn test_fixpoint_incremental_add() {
        use crate::traits::FixpointUpdate;

        let bdd = Rc::new(Bdd::default());
        let mut ts = IncrementalTransSystem::new(bdd.clone());

        let (s0_var, s0_next) = ts.declare_var(Var::new("b0"));
        let (s1_var, s1_next) = ts.declare_var(Var::new("b1"));

        let s00 = bdd.apply_and(-bdd.mk_var(s0_var), -bdd.mk_var(s1_var));
        let s01 = bdd.apply_and(-bdd.mk_var(s0_var), bdd.mk_var(s1_var));
        let s10 = bdd.apply_and(bdd.mk_var(s0_var), -bdd.mk_var(s1_var));

        let s01_next = bdd.apply_and(-bdd.mk_var(s0_next), bdd.mk_var(s1_next));
        let s10_next = bdd.apply_and(bdd.mk_var(s0_next), -bdd.mk_var(s1_next));

        ts.set_initial(s00);

        // Initial transition: 00 -> 01 only
        let t1 = bdd.apply_and(s00, s01_next);
        ts.set_transition(t1);

        // Create fixpoint with initial computation
        let mut fp = IncrementalReachabilityFixpoint::with_initial_compute(ts);
        assert!(fp.is_valid());

        // Initial reach: {s00, s01}
        let reach1 = fp.current();
        assert!(!bdd.is_zero(bdd.apply_and(reach1, s00)));
        assert!(!bdd.is_zero(bdd.apply_and(reach1, s01)));
        assert!(bdd.is_zero(bdd.apply_and(reach1, s10))); // s10 not reachable yet

        // Add transition 01 -> 10
        let t2 = bdd.apply_and(s01, s10_next);
        let update = fp.add_transitions(t2);

        // Should be incremental update
        assert!(
            matches!(update, FixpointUpdate::PartiallyRecomputed { .. }),
            "Expected partial recompute, got {:?}",
            update
        );

        // Now s10 should be reachable
        let reach2 = fp.current();
        assert!(!bdd.is_zero(bdd.apply_and(reach2, s10)));
    }

    #[test]
    fn test_fixpoint_force_recompute() {
        use crate::traits::FixpointUpdate;

        let bdd = Rc::new(Bdd::default());
        let mut ts = IncrementalTransSystem::new(bdd.clone());

        let (s_var, s_next) = ts.declare_var(Var::new("s"));
        let s0 = -bdd.mk_var(s_var);
        let s1 = bdd.mk_var(s_var);
        let s1_next = bdd.mk_var(s_next);

        ts.set_initial(s0);
        let trans = bdd.apply_and(s0, s1_next);
        ts.set_transition(trans);

        let mut fp = IncrementalReachabilityFixpoint::with_initial_compute(ts);

        // Force recompute
        let update = fp.recompute();
        assert!(matches!(update, FixpointUpdate::FullyRecomputed { .. }));
        assert!(fp.is_valid());

        let reach = fp.current();
        assert!(!bdd.is_zero(bdd.apply_and(reach, s0)));
        assert!(!bdd.is_zero(bdd.apply_and(reach, s1)));
    }
}
