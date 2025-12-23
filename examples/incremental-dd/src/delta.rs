//! Delta representation for incremental decision diagrams.
//!
//! A **delta** represents a semantic change to a DD-backed object.
//! It consists of an optional "added" component and an optional "removed" component,
//! with the invariant that `added ∩ removed = ∅`.
//!
//! # Example
//!
//! ```
//! use incremental_dd::delta::{Delta, DeltaEffect};
//! use ananke_bdd::bdd::Bdd;
//!
//! let bdd = Bdd::default();
//! let x = bdd.mk_var(1);
//! let y = bdd.mk_var(2);
//!
//! // Create a delta that adds {x ∧ y} and removes {x ∧ ¬y}
//! // These are disjoint sets, so the delta is valid
//! let added = bdd.apply_and(x, y);
//! let removed = bdd.apply_and(x, -y);
//! let delta = Delta::new()
//!     .with_added(added)
//!     .with_removed(removed);
//!
//! assert!(delta.is_valid(&bdd));
//! ```

use std::fmt;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

/// A semantic delta representing changes to a DD-backed object.
///
/// A delta consists of:
/// - `added`: States/transitions being added (optional)
/// - `removed`: States/transitions being removed (optional)
///
/// # Invariant
///
/// `added ∩ removed = ∅` — a state cannot be both added and removed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Delta {
    /// States/transitions being added
    pub added: Option<Ref>,
    /// States/transitions being removed
    pub removed: Option<Ref>,
}

impl Delta {
    /// Create an empty delta (no changes).
    pub fn empty() -> Self {
        Delta {
            added: None,
            removed: None,
        }
    }

    /// Create a new delta builder.
    pub fn new() -> Self {
        Self::empty()
    }

    /// Create a delta that only adds.
    pub fn addition(added: Ref) -> Self {
        Delta {
            added: Some(added),
            removed: None,
        }
    }

    /// Create a delta that only removes.
    pub fn removal(removed: Ref) -> Self {
        Delta {
            added: None,
            removed: Some(removed),
        }
    }

    /// Set the added component.
    pub fn with_added(mut self, added: Ref) -> Self {
        self.added = Some(added);
        self
    }

    /// Set the removed component.
    pub fn with_removed(mut self, removed: Ref) -> Self {
        self.removed = Some(removed);
        self
    }

    /// Check if the delta is empty (no changes).
    pub fn is_empty(&self) -> bool {
        self.added.is_none() && self.removed.is_none()
    }

    /// Check if the delta is valid (added ∩ removed = ∅).
    pub fn is_valid(&self, bdd: &Bdd) -> bool {
        if let (Some(a), Some(n)) = (self.added, self.removed) {
            let intersection = bdd.apply_and(a, n);
            bdd.is_zero(intersection)
        } else {
            true
        }
    }

    /// Validate the delta, returning an error if invalid.
    pub fn validate(&self, bdd: &Bdd) -> Result<(), DeltaError> {
        if !self.is_valid(bdd) {
            Err(DeltaError::NonDisjoint)
        } else {
            Ok(())
        }
    }

    /// Check if this is an addition-only delta (monotonic growth).
    pub fn is_addition_only(&self) -> bool {
        self.removed.is_none()
    }

    /// Check if this is a removal-only delta (monotonic shrink).
    pub fn is_removal_only(&self) -> bool {
        self.added.is_none()
    }

    /// Apply this delta to a set: `(set ∪ added) ∖ removed`.
    pub fn apply(&self, bdd: &Bdd, set: Ref) -> Ref {
        let mut result = set;

        // Add new elements
        if let Some(added) = self.added {
            result = bdd.apply_or(result, added);
        }

        // Remove elements
        if let Some(removed) = self.removed {
            result = bdd.apply_and(result, -removed);
        }

        result
    }

    /// Compose two deltas: apply self first, then other.
    ///
    /// The result is a single delta equivalent to applying both in sequence.
    pub fn compose(&self, bdd: &Bdd, other: &Delta) -> Delta {
        // New additions: (self.added ∖ other.removed) ∪ other.added
        // New removals: (self.removed ∖ other.added) ∪ other.removed

        let new_added = match (self.added, other.added, other.removed) {
            (Some(a1), Some(a2), Some(r2)) => {
                let a1_surviving = bdd.apply_and(a1, -r2);
                Some(bdd.apply_or(a1_surviving, a2))
            }
            (Some(a1), Some(a2), None) => Some(bdd.apply_or(a1, a2)),
            (Some(a1), None, Some(r2)) => {
                let result = bdd.apply_and(a1, -r2);
                if bdd.is_zero(result) {
                    None
                } else {
                    Some(result)
                }
            }
            (None, a2, _) => a2,
            (a1, None, None) => a1,
        };

        let new_removed = match (self.removed, other.added, other.removed) {
            (Some(r1), Some(a2), Some(r2)) => {
                let r1_surviving = bdd.apply_and(r1, -a2);
                Some(bdd.apply_or(r1_surviving, r2))
            }
            (Some(r1), Some(a2), None) => {
                let result = bdd.apply_and(r1, -a2);
                if bdd.is_zero(result) {
                    None
                } else {
                    Some(result)
                }
            }
            (Some(r1), None, Some(r2)) => Some(bdd.apply_or(r1, r2)),
            (None, _, r2) => r2,
            (r1, None, None) => r1,
        };

        Delta {
            added: new_added,
            removed: new_removed,
        }
    }

    /// Invert the delta: additions become removals and vice versa.
    pub fn invert(&self) -> Delta {
        Delta {
            added: self.removed,
            removed: self.added,
        }
    }

    /// Compute the size of the change (number of affected elements).
    ///
    /// Returns (added_count, removed_count) if computable, None if too large.
    pub fn change_size(&self, bdd: &Bdd, num_vars: usize) -> Option<(u64, u64)> {
        use num_traits::ToPrimitive;

        let added_count = match self.added {
            Some(a) => bdd.sat_count(a, num_vars).to_u64()?,
            None => 0,
        };

        let removed_count = match self.removed {
            Some(r) => bdd.sat_count(r, num_vars).to_u64()?,
            None => 0,
        };

        Some((added_count, removed_count))
    }
}

impl Default for Delta {
    fn default() -> Self {
        Self::empty()
    }
}

impl fmt::Display for Delta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.added, self.removed) {
            (None, None) => write!(f, "Δ(empty)"),
            (Some(_), None) => write!(f, "Δ(+only)"),
            (None, Some(_)) => write!(f, "Δ(-only)"),
            (Some(_), Some(_)) => write!(f, "Δ(±mixed)"),
        }
    }
}

/// Errors that can occur when working with deltas.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeltaError {
    /// The added and removed sets are not disjoint.
    NonDisjoint,
}

impl fmt::Display for DeltaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeltaError::NonDisjoint => {
                write!(f, "Delta invariant violation: added ∩ removed ≠ ∅")
            }
        }
    }
}

impl std::error::Error for DeltaError {}

/// The effect of applying a delta to a semantic object.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeltaEffect {
    /// The delta had no observable effect.
    NoChange,

    /// The delta caused a local change that can be handled incrementally.
    LocalChange {
        /// Number of BDD nodes affected by the change.
        affected_nodes: usize,
    },

    /// The delta requires a full rebuild of the semantic object.
    GlobalRebuildRequired,
}

impl DeltaEffect {
    /// Check if incremental update is possible.
    pub fn is_incremental(&self) -> bool {
        !matches!(self, DeltaEffect::GlobalRebuildRequired)
    }
}

impl fmt::Display for DeltaEffect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeltaEffect::NoChange => write!(f, "NoChange"),
            DeltaEffect::LocalChange { affected_nodes } => {
                write!(f, "LocalChange({} nodes)", affected_nodes)
            }
            DeltaEffect::GlobalRebuildRequired => write!(f, "GlobalRebuildRequired"),
        }
    }
}

/// A delta for system components (states, transitions, properties).
#[derive(Debug, Clone, Default)]
pub struct SystemDelta {
    /// Changes to the state space
    pub state_delta: Option<Delta>,
    /// Changes to the transition relation
    pub transition_delta: Option<Delta>,
    /// Changes to the property being verified
    pub property_delta: Option<Delta>,
}

impl SystemDelta {
    /// Create an empty system delta.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a system delta with only state changes.
    pub fn states(delta: Delta) -> Self {
        SystemDelta {
            state_delta: Some(delta),
            ..Default::default()
        }
    }

    /// Create a system delta with only transition changes.
    pub fn transitions(delta: Delta) -> Self {
        SystemDelta {
            transition_delta: Some(delta),
            ..Default::default()
        }
    }

    /// Create a system delta with only property changes.
    pub fn property(delta: Delta) -> Self {
        SystemDelta {
            property_delta: Some(delta),
            ..Default::default()
        }
    }

    /// Check if the system delta is empty.
    pub fn is_empty(&self) -> bool {
        self.state_delta.as_ref().map_or(true, |d| d.is_empty())
            && self.transition_delta.as_ref().map_or(true, |d| d.is_empty())
            && self.property_delta.as_ref().map_or(true, |d| d.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_delta() {
        let bdd = Bdd::default();
        let delta = Delta::empty();

        assert!(delta.is_empty());
        assert!(delta.is_valid(&bdd));

        let set = bdd.mk_var(1);
        assert_eq!(delta.apply(&bdd, set), set);
    }

    #[test]
    fn test_addition_only() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let delta = Delta::addition(y);

        assert!(delta.is_addition_only());
        assert!(!delta.is_removal_only());
        assert!(delta.is_valid(&bdd));

        // Apply to x: should get x ∨ y
        let result = delta.apply(&bdd, x);
        assert_eq!(result, bdd.apply_or(x, y));
    }

    #[test]
    fn test_removal_only() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        // Initial set: x (all assignments where x=true)
        let delta = Delta::removal(y);

        assert!(!delta.is_addition_only());
        assert!(delta.is_removal_only());
        assert!(delta.is_valid(&bdd));

        // Apply to x: should get x ∧ ¬y (remove assignments where y=true)
        let result = delta.apply(&bdd, x);
        assert_eq!(result, bdd.apply_and(x, -y));
    }

    #[test]
    fn test_mixed_delta() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        // Add (x ∧ y), remove (x ∧ ¬y) - disjoint sets
        let added = bdd.apply_and(x, y);
        let removed = bdd.apply_and(x, -y);
        let delta = Delta::new().with_added(added).with_removed(removed);

        assert!(!delta.is_addition_only());
        assert!(!delta.is_removal_only());
        assert!(delta.is_valid(&bdd));
    }

    #[test]
    fn test_invalid_delta() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);

        // Try to add and remove the same thing
        let delta = Delta::new().with_added(x).with_removed(x);

        assert!(!delta.is_valid(&bdd));
        assert!(delta.validate(&bdd).is_err());
    }

    #[test]
    fn test_delta_invert() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let delta = Delta::new().with_added(x).with_removed(y);
        let inv = delta.invert();

        assert_eq!(inv.added, Some(y));
        assert_eq!(inv.removed, Some(x));
    }

    #[test]
    fn test_delta_compose() {
        let bdd = Bdd::default();
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        // delta1: add x
        let delta1 = Delta::addition(x);
        // delta2: add y
        let delta2 = Delta::addition(y);

        let composed = delta1.compose(&bdd, &delta2);

        // Net effect: add (x ∨ y)
        let expected_added = bdd.apply_or(x, y);
        assert_eq!(composed.added, Some(expected_added));
        assert!(composed.removed.is_none());
    }
}
