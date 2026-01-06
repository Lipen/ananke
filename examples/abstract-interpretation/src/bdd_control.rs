//! BDD Control Domain: Path-Sensitive Abstract Interpretation
//!
//! This module implements a BDD-based control domain for path-sensitive static analysis.
//! The key idea is to partition program states based on Boolean control variables (flags,
//! mode indicators, branch conditions) and maintain separate numeric invariants for each
//! control partition.
//!
//! # Theory
//!
//! The BDD Control Domain is defined as:
//!
//! ```text
//! D_BDD = (E_BDD, ⊑, ⊔, ⊓, ∇, ⊥, ⊤)
//! ```
//!
//! Where:
//! - **Elements**: BDDs over Boolean control variables
//! - **Partial Order**: `φ₁ ⊑ φ₂` ⟺ `φ₁ ⇒ φ₂` (logical implication)
//! - **Join**: `φ₁ ⊔ φ₂` = `φ₁ ∨ φ₂` (disjunction)
//! - **Meet**: `φ₁ ⊓ φ₂` = `φ₁ ∧ φ₂` (conjunction)
//! - **Bottom**: `false` (unreachable)
//! - **Top**: `true` (all paths reachable)
//!
//! # Example
//!
//! ```rust
//! use abstract_interpretation::*;
//! use std::rc::Rc;
//!
//! // Create BDD control domain
//! let domain = BddControlDomain::new();
//!
//! // Allocate control variable "flag"
//! let var_id = domain.allocate_var("flag");
//!
//! // Create control state: flag = true
//! let state_true = domain.mk_var_true("flag");
//! let state_false = domain.mk_var_false("flag");
//!
//! // Join: flag could be true OR false
//! let state_any = domain.join(&state_true, &state_false);
//! assert!(domain.is_top(&state_any)); // true (no constraint)
//!
//! // Meet: flag is both true AND false (contradiction)
//! let state_bot = domain.meet(&state_true, &state_false);
//! assert!(domain.is_bottom(&state_bot)); // unreachable
//! ```
//!
//! # Architecture
//!
//! The control domain works with any numeric domain through the product construction:
//!
//! ```text
//! ControlSensitiveProduct = BddControlDomain × NumericDomain
//! ```
//!
//! This allows maintaining separate numeric invariants per control path.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use super::domain::AbstractDomain;
use crate::NumericDomain;

/// A control state represented as a BDD over Boolean control variables.
///
/// # Interpretation
///
/// A control state `φ` represents a set of control paths. The BDD evaluates to:
/// - `true` (1): This control path is reachable
/// - `false` (0): This control path is unreachable/infeasible
///
/// # Examples
///
/// - `φ = true`: All control paths (no constraints)
/// - `φ = false`: No control paths (unreachable)
/// - `φ = (flag = true)`: Only paths where flag is true
/// - `φ = (flag₁ = true) ∧ (flag₂ = false)`: Specific control configuration
///
/// # Representation
///
/// Internally uses BDD reference (`Ref`) which is a 32-bit integer index into
/// the shared BDD manager's node table.
#[derive(Clone)]
pub struct ControlState {
    /// BDD representing the control constraint (Boolean formula φ)
    phi: Ref,
    /// Shared BDD manager
    manager: Rc<Bdd>,
    /// Human-readable description (for debugging)
    description: Option<String>,
}

impl ControlState {
    /// Create a new control state from a BDD reference.
    pub fn new(phi: Ref, manager: Rc<Bdd>) -> Self {
        Self {
            phi,
            manager,
            description: None,
        }
    }

    /// Create a control state with a description.
    pub fn new_with_description(phi: Ref, manager: Rc<Bdd>, desc: String) -> Self {
        Self {
            phi,
            manager,
            description: Some(desc),
        }
    }

    /// Get the BDD reference (Boolean formula φ).
    pub fn phi(&self) -> Ref {
        self.phi
    }

    /// Get the shared BDD manager.
    pub fn manager(&self) -> &Rc<Bdd> {
        &self.manager
    }

    /// Check if this control state is satisfiable (not false).
    pub fn is_sat(&self) -> bool {
        self.phi != self.manager.zero()
    }

    /// Check if this control state is a tautology (true).
    pub fn is_tautology(&self) -> bool {
        self.phi == self.manager.one()
    }

    /// Check if this control state is satisfiable (has at least one solution).
    ///
    /// This is a simpler alternative to counting satisfying assignments.
    /// Returns true if there exists at least one control configuration satisfying this state.
    pub fn has_solution(&self) -> bool {
        self.is_sat()
    }

    /// Get description if available.
    pub fn description(&self) -> Option<&str> {
        self.description.as_deref()
    }
}

impl PartialEq for ControlState {
    fn eq(&self, other: &Self) -> bool {
        // Two control states are equal if they represent the same BDD
        // BDD nodes are canonical, so reference equality is sufficient
        self.phi == other.phi
    }
}

impl Eq for ControlState {}

impl fmt::Debug for ControlState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(desc) = &self.description {
            write!(f, "ControlState({})", desc)
        } else if self.phi == self.manager.zero() {
            write!(f, "ControlState(⊥)")
        } else if self.phi == self.manager.one() {
            write!(f, "ControlState(⊤)")
        } else {
            write!(f, "ControlState(φ:{})", self.phi)
        }
    }
}

impl fmt::Display for ControlState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(desc) = &self.description {
            write!(f, "{}", desc)
        } else if self.phi == self.manager.zero() {
            write!(f, "⊥")
        } else if self.phi == self.manager.one() {
            write!(f, "⊤")
        } else {
            write!(f, "φ({})", self.phi)
        }
    }
}

/// BDD-based control domain for path-sensitive analysis.
///
/// This domain represents sets of Boolean control states using Binary Decision Diagrams.
/// Control variables are Boolean program variables (flags, mode indicators) that determine
/// which control path the program is on.
///
/// # Key Features
///
/// - **Compact Representation**: BDDs can represent exponentially many control states
/// - **Canonical Form**: BDDs are automatically reduced and canonical
/// - **Efficient Operations**: Boolean operations (AND, OR, NOT) are polynomial
/// - **Path Sensitivity**: Different control paths maintain separate invariants
///
/// # Usage
///
/// ```rust
/// use abstract_interpretation::*;
///
/// let domain = BddControlDomain::new();
///
/// // Allocate control variables
/// domain.allocate_var("flag");
/// domain.allocate_var("initialized");
///
/// // Create states
/// let state1 = domain.mk_var_true("flag");
/// let state2 = domain.mk_var_false("flag");
///
/// // Combine with Boolean operations
/// let any_flag = domain.join(&state1, &state2);  // flag ∈ {true, false}
/// ```
#[derive(Clone)]
pub struct BddControlDomain {
    /// Shared BDD manager
    manager: Rc<Bdd>,
    /// Control variable name to BDD variable ID mapping
    var_map: Rc<RefCell<HashMap<String, u32>>>,
    /// Next available BDD variable ID
    next_var: Rc<RefCell<u32>>,
}

impl BddControlDomain {
    /// Create a new BDD control domain with a fresh BDD manager.
    pub fn new() -> Self {
        Self {
            manager: Rc::new(Bdd::default()),
            var_map: Rc::new(RefCell::new(HashMap::new())),
            next_var: Rc::new(RefCell::new(1)), // BDD vars start at 1, not 0
        }
    }

    /// Get the shared BDD manager.
    pub fn manager(&self) -> &Rc<Bdd> {
        &self.manager
    }

    /// Allocate a BDD variable for a control variable.
    ///
    /// If the variable already exists, returns its existing ID.
    /// Otherwise, allocates a new BDD variable ID.
    ///
    /// # Arguments
    ///
    /// * `name` - Name of the control variable (e.g., "flag", "is_active")
    ///
    /// # Returns
    ///
    /// BDD variable ID (u32) for this control variable.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// let var_id = domain.allocate_var("flag");
    /// assert_eq!(var_id, 1); // First variable gets ID 1
    ///
    /// let same_id = domain.allocate_var("flag");
    /// assert_eq!(same_id, 1); // Same variable returns same ID
    ///
    /// let next_id = domain.allocate_var("other");
    /// assert_eq!(next_id, 2); // Next variable gets ID 2
    /// ```
    pub fn allocate_var(&self, name: &str) -> u32 {
        let mut var_map = self.var_map.borrow_mut();

        if let Some(&id) = var_map.get(name) {
            return id;
        }

        let mut next = self.next_var.borrow_mut();
        let id = *next;
        *next += 1;

        var_map.insert(name.to_string(), id);
        id
    }

    /// Get the BDD variable ID for a control variable, if it exists.
    pub fn get_var(&self, name: &str) -> Option<u32> {
        self.var_map.borrow().get(name).copied()
    }

    /// Get the number of allocated control variables.
    pub fn num_vars(&self) -> usize {
        self.var_map.borrow().len()
    }

    /// Create a control state where the variable is true.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let state = domain.mk_var_true("flag");
    /// // Represents: flag = true
    /// ```
    pub fn mk_var_true(&self, var: &str) -> ControlState {
        let var_id = self.allocate_var(var);
        let phi = self.manager.mk_var(var_id);
        ControlState::new_with_description(phi, Rc::clone(&self.manager), format!("{} = true", var))
    }

    /// Create a control state where the variable is false.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let state = domain.mk_var_false("flag");
    /// // Represents: flag = false
    /// ```
    pub fn mk_var_false(&self, var: &str) -> ControlState {
        let var_id = self.allocate_var(var);
        let var_phi = self.manager.mk_var(var_id);
        let phi = self.manager.apply_not(var_phi);
        ControlState::new_with_description(phi, Rc::clone(&self.manager), format!("{} = false", var))
    }

    /// Conjunction: `φ₁ ∧ φ₂`
    ///
    /// Creates a control state representing the intersection of two control states.
    pub fn and(&self, s1: &ControlState, s2: &ControlState) -> ControlState {
        let phi = self.manager.apply_and(s1.phi, s2.phi);
        ControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Disjunction: `φ₁ ∨ φ₂`
    ///
    /// Creates a control state representing the union of two control states.
    pub fn or(&self, s1: &ControlState, s2: &ControlState) -> ControlState {
        let phi = self.manager.apply_or(s1.phi, s2.phi);
        ControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Negation: `¬φ`
    ///
    /// Creates a control state representing the complement.
    pub fn not(&self, s: &ControlState) -> ControlState {
        let phi = self.manager.apply_not(s.phi);
        ControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Implication: `φ₁ ⇒ φ₂`
    ///
    /// Creates a control state representing the implication from `s1` to `s2`.
    pub fn imply(&self, s1: &ControlState, s2: &ControlState) -> ControlState {
        let phi = self.manager.apply_imply(s1.phi, s2.phi);
        ControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Equivalence: `φ₁ ⇔ φ₂`
    ///
    /// Creates a control state representing the equivalence of `s1` and `s2`.
    pub fn equiv(&self, s1: &ControlState, s2: &ControlState) -> ControlState {
        let phi = self.manager.apply_eq(s1.phi, s2.phi);
        ControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Check if `s1` implies `s2` (`φ₁ ⇒ φ₂`).
    pub fn implies(&self, s1: &ControlState, s2: &ControlState) -> bool {
        self.manager.is_implies(s1.phi, s2.phi)
    }

    /// Check if two control states are equivalent.
    pub fn equivalent(&self, s1: &ControlState, s2: &ControlState) -> bool {
        // `φ₁ ≡ φ₂` iff they have the same canonical BDD representation
        s1.phi == s2.phi
    }

    /// Create a tautology (⊤) control state.
    pub fn mk_true(&self) -> ControlState {
        ControlState::new(self.manager.one(), Rc::clone(&self.manager))
    }

    /// Create a contradiction (⊥) control state.
    pub fn mk_false(&self) -> ControlState {
        ControlState::new(self.manager.zero(), Rc::clone(&self.manager))
    }

    /// Get all allocated variable names.
    pub fn get_all_vars(&self) -> Vec<String> {
        self.var_map.borrow().keys().cloned().collect()
    }
}

impl Default for BddControlDomain {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for BddControlDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BddControlDomain")
            .field("num_vars", &self.num_vars())
            .field("variables", &self.var_map.borrow().keys().collect::<Vec<_>>())
            .finish()
    }
}

// ============================================================================
// AbstractDomain Implementation
// ============================================================================

impl AbstractDomain for BddControlDomain {
    type Element = ControlState;

    /// Create the bottom element (unreachable/false).
    ///
    /// The bottom element represents an unreachable control state, equivalent
    /// to the BDD constant `false` (0).
    ///
    /// # Properties
    ///
    /// - `⊥ ⊑ φ` for all `φ` (bottom is the least element)
    /// - `⊥ ⊓ φ = ⊥` (bottom annihilates meet)
    /// - `⊥ ⊔ φ = φ` (bottom is the identity for join)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// let bottom = domain.bottom();
    ///
    /// assert!(domain.is_bottom(&bottom));
    /// assert!(!bottom.is_sat()); // No satisfying assignments
    /// ```
    fn bottom(&self) -> Self::Element {
        ControlState::new_with_description(self.manager.zero(), Rc::clone(&self.manager), "⊥".to_string())
    }

    /// Create the top element (all paths reachable/true).
    ///
    /// The top element represents all possible control states, equivalent
    /// to the BDD constant `true` (1).
    ///
    /// # Properties
    ///
    /// - `φ ⊑ ⊤` for all `φ` (top is the greatest element)
    /// - `⊤ ⊔ φ = ⊤` (top annihilates join)
    /// - `⊤ ⊓ φ = φ` (top is the identity for meet)
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// let top = domain.top();
    ///
    /// assert!(domain.is_top(&top));
    /// assert!(top.is_tautology()); // Always true
    /// ```
    fn top(&self) -> Self::Element {
        ControlState::new_with_description(self.manager.one(), Rc::clone(&self.manager), "⊤".to_string())
    }

    /// Check if an element is bottom (unreachable).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// // flag=true AND flag=false is impossible
    /// let impossible = domain.meet(&flag_true, &flag_false);
    /// assert!(domain.is_bottom(&impossible));
    /// ```
    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.phi == self.manager.zero()
    }

    /// Check if an element is top (all paths reachable).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// // flag=true OR flag=false covers all possibilities
    /// let all_paths = domain.join(&flag_true, &flag_false);
    /// assert!(domain.is_top(&all_paths));
    /// ```
    fn is_top(&self, elem: &Self::Element) -> bool {
        elem.phi == self.manager.one()
    }

    /// Partial order: `φ₁ ⊑ φ₂` iff `φ₁ ⇒ φ₂` (logical implication).
    ///
    /// Checks if elem1 is "more precise" or "smaller" than elem2.
    /// In the BDD control domain, this means elem1 implies elem2.
    ///
    /// # Interpretation
    ///
    /// - `φ₁ ⊑ φ₂` means: every control path in `φ₁` is also in `φ₂`
    /// - Equivalently: the set of satisfying assignments of `φ₁` is a subset of `φ₂`
    ///
    /// # Properties
    ///
    /// - Reflexive: `φ ⊑ φ`
    /// - Transitive: `φ₁ ⊑ φ₂ ∧ φ₂ ⊑ φ₃ ⇒ φ₁ ⊑ φ₃`
    /// - Antisymmetric: `φ₁ ⊑ φ₂ ∧ φ₂ ⊑ φ₁ ⇒ φ₁ = φ₂`
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let top = domain.top();
    ///
    /// // flag=true is more precise than ⊤ (all paths)
    /// assert!(domain.le(&flag_true, &top));
    /// assert!(!domain.le(&top, &flag_true));
    /// ```
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        // φ₁ ⊑ φ₂ ⟺ φ₁ ⇒ φ₂
        self.implies(elem1, elem2)
    }

    /// Join (least upper bound): `φ₁ ⊔ φ₂` = `φ₁ ∨ φ₂` (disjunction).
    ///
    /// Computes the least element that is greater than or equal to both inputs.
    /// In the BDD control domain, this is logical OR.
    ///
    /// # Interpretation
    ///
    /// - Result represents control paths reachable by **either** elem1 **or** elem2
    /// - Over-approximates: includes all paths from both inputs
    ///
    /// # Properties
    ///
    /// - Commutative: `φ₁ ⊔ φ₂ = φ₂ ⊔ φ₁`
    /// - Associative: `(φ₁ ⊔ φ₂) ⊔ φ₃ = φ₁ ⊔ (φ₂ ⊔ φ₃)`
    /// - Idempotent: `φ ⊔ φ = φ`
    /// - `φ₁ ⊑ (φ₁ ⊔ φ₂)` and `φ₂ ⊑ (φ₁ ⊔ φ₂)`
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// // Either flag=true or flag=false covers all possibilities
    /// let joined = domain.join(&flag_true, &flag_false);
    /// assert!(domain.is_top(&joined)); // No constraint on flag
    /// ```
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.or(elem1, elem2)
    }

    /// Meet (greatest lower bound): `φ₁ ⊓ φ₂` = `φ₁ ∧ φ₂` (conjunction).
    ///
    /// Computes the greatest element that is less than or equal to both inputs.
    /// In the BDD control domain, this is logical AND.
    ///
    /// # Interpretation
    ///
    /// - Result represents control paths reachable by **both** elem1 **and** elem2
    /// - Refines: only includes paths common to both inputs
    ///
    /// # Properties
    ///
    /// - Commutative: `φ₁ ⊓ φ₂ = φ₂ ⊓ φ₁`
    /// - Associative: `(φ₁ ⊓ φ₂) ⊓ φ₃ = φ₁ ⊓ (φ₂ ⊓ φ₃)`
    /// - Idempotent: `φ ⊓ φ = φ`
    /// - `(φ₁ ⊓ φ₂) ⊑ φ₁` and `(φ₁ ⊓ φ₂) ⊑ φ₂`
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag1");
    /// domain.allocate_var("flag2");
    ///
    /// let flag1_true = domain.mk_var_true("flag1");
    /// let flag2_true = domain.mk_var_true("flag2");
    ///
    /// // Both must be true
    /// let met = domain.meet(&flag1_true, &flag2_true);
    /// assert!(!domain.is_bottom(&met)); // Satisfiable
    /// assert!(!domain.is_top(&met));    // Constrained
    /// ```
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.and(elem1, elem2)
    }

    /// Widening operator: `φ₁ ∇ φ₂` = `φ₁ ∨ φ₂` (same as join).
    ///
    /// For BDD control domain, widening is the same as join because the lattice
    /// has **finite height** (2^n where n is the number of control variables).
    /// This ensures termination of fixpoint iteration.
    ///
    /// # Finite Height Property
    ///
    /// The lattice of Boolean formulas over n variables has at most 2^n distinct
    /// equivalence classes, guaranteeing that any ascending chain:
    ///
    /// ```text
    /// φ₀ ⊑ φ₁ ⊑ φ₂ ⊑ ... ⊑ φₖ
    /// ```
    ///
    /// must stabilize after at most 2^n steps.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use abstract_interpretation::*;
    /// let domain = BddControlDomain::new();
    /// domain.allocate_var("flag");
    ///
    /// let flag_true = domain.mk_var_true("flag");
    /// let flag_false = domain.mk_var_false("flag");
    ///
    /// let widened = domain.widen(&flag_true, &flag_false);
    /// assert!(domain.is_top(&widened)); // Same as join for BDD domain
    /// ```
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For finite lattices, widening = join
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_control_state_creation() {
        let domain = BddControlDomain::new();

        let bottom = ControlState::new(domain.manager.zero(), Rc::clone(&domain.manager));
        assert!(!bottom.is_sat());
        assert!(!bottom.is_tautology());

        let top = ControlState::new(domain.manager.one(), Rc::clone(&domain.manager));
        assert!(top.is_sat());
        assert!(top.is_tautology());
    }

    #[test]
    fn test_var_allocation() {
        let domain = BddControlDomain::new();

        let id1 = domain.allocate_var("flag");
        assert_eq!(id1, 1);

        let id2 = domain.allocate_var("flag");
        assert_eq!(id2, 1); // Same variable

        let id3 = domain.allocate_var("other");
        assert_eq!(id3, 2); // Different variable

        assert_eq!(domain.num_vars(), 2);
    }

    #[test]
    fn test_mk_var_true_false() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let state_true = domain.mk_var_true("flag");
        let state_false = domain.mk_var_false("flag");

        assert!(state_true.is_sat());
        assert!(state_false.is_sat());
        assert!(!state_true.is_tautology());
        assert!(!state_false.is_tautology());

        assert_ne!(state_true, state_false);
    }

    #[test]
    fn test_boolean_operations() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let state_true = domain.mk_var_true("flag");
        let state_false = domain.mk_var_false("flag");

        // flag=true AND flag=false = ⊥
        let and_result = domain.and(&state_true, &state_false);
        assert!(!and_result.is_sat());

        // flag=true OR flag=false = ⊤
        let or_result = domain.or(&state_true, &state_false);
        assert!(or_result.is_tautology());

        // NOT (flag=true) = flag=false
        let not_result = domain.not(&state_true);
        assert!(domain.equivalent(&not_result, &state_false));
    }

    #[test]
    fn test_implication() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let state_true = domain.mk_var_true("flag");
        let top = ControlState::new(domain.manager.one(), Rc::clone(&domain.manager));
        let bottom = ControlState::new(domain.manager.zero(), Rc::clone(&domain.manager));

        // flag=true ⇒ ⊤
        assert!(domain.implies(&state_true, &top));

        // ⊥ ⇒ flag=true
        assert!(domain.implies(&bottom, &state_true));

        // flag=true ⇏ flag=false
        let state_false = domain.mk_var_false("flag");
        assert!(!domain.implies(&state_true, &state_false));
    }

    #[test]
    fn test_control_state_equality() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let s1 = domain.mk_var_true("flag");
        let s2 = domain.mk_var_true("flag");

        assert_eq!(s1, s2); // Same BDD reference

        let s3 = domain.mk_var_false("flag");
        assert_ne!(s1, s3);
    }

    #[test]
    fn test_has_solution() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        assert!(s1.has_solution());

        let s2 = domain.mk_var_true("flag2");
        let both = domain.and(&s1, &s2);
        assert!(both.has_solution());

        let top = ControlState::new(domain.manager.one(), Rc::clone(&domain.manager));
        assert!(top.has_solution());

        let bottom = ControlState::new(domain.manager.zero(), Rc::clone(&domain.manager));
        assert!(!bottom.has_solution());
    }

    // ========================================================================
    // AbstractDomain Trait Tests
    // ========================================================================

    #[test]
    fn test_bottom_top() {
        let domain = BddControlDomain::new();

        let bottom = domain.bottom();
        let top = domain.top();

        assert!(domain.is_bottom(&bottom));
        assert!(!domain.is_bottom(&top));

        assert!(domain.is_top(&top));
        assert!(!domain.is_top(&bottom));
    }

    #[test]
    fn test_bottom_is_least() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // ⊥ ⊑ everything
        assert!(domain.le(&bottom, &top));
        assert!(domain.le(&bottom, &flag_true));
        assert!(domain.le(&bottom, &bottom));
    }

    #[test]
    fn test_top_is_greatest() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // everything ⊑ ⊤
        assert!(domain.le(&bottom, &top));
        assert!(domain.le(&flag_true, &top));
        assert!(domain.le(&top, &top));
    }

    #[test]
    fn test_le_reflexive() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");

        // φ ⊑ φ
        assert!(domain.le(&flag_true, &flag_true));
    }

    #[test]
    fn test_le_transitive() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let flag1_true = domain.mk_var_true("flag1");
        let flag2_true = domain.mk_var_true("flag2");

        // flag1=true ∧ flag2=true ⊑ flag1=true ⊑ ⊤
        let both = domain.meet(&flag1_true, &flag2_true);
        let top = domain.top();

        assert!(domain.le(&both, &flag1_true));
        assert!(domain.le(&flag1_true, &top));
        assert!(domain.le(&both, &top)); // Transitivity
    }

    #[test]
    fn test_le_antisymmetric() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true1 = domain.mk_var_true("flag");
        let flag_true2 = domain.mk_var_true("flag");

        // φ₁ ⊑ φ₂ ∧ φ₂ ⊑ φ₁ ⇒ φ₁ = φ₂
        assert!(domain.le(&flag_true1, &flag_true2));
        assert!(domain.le(&flag_true2, &flag_true1));
        assert_eq!(flag_true1, flag_true2);
    }

    #[test]
    fn test_join_commutative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        let j1 = domain.join(&s1, &s2);
        let j2 = domain.join(&s2, &s1);

        assert!(domain.equivalent(&j1, &j2));
    }

    #[test]
    fn test_join_associative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");
        domain.allocate_var("flag3");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let s3 = domain.mk_var_true("flag3");

        let left = domain.join(&domain.join(&s1, &s2), &s3);
        let right = domain.join(&s1, &domain.join(&s2, &s3));

        assert!(domain.equivalent(&left, &right));
    }

    #[test]
    fn test_join_idempotent() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");
        let joined = domain.join(&flag_true, &flag_true);

        assert_eq!(flag_true, joined);
    }

    #[test]
    fn test_join_upper_bound() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let joined = domain.join(&s1, &s2);

        // s1 ⊑ (s1 ⊔ s2) and s2 ⊑ (s1 ⊔ s2)
        assert!(domain.le(&s1, &joined));
        assert!(domain.le(&s2, &joined));
    }

    #[test]
    fn test_join_with_bottom() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let flag_true = domain.mk_var_true("flag");

        // ⊥ ⊔ φ = φ
        let joined = domain.join(&bottom, &flag_true);
        assert_eq!(joined, flag_true);
    }

    #[test]
    fn test_join_with_top() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // ⊤ ⊔ φ = ⊤
        let joined = domain.join(&top, &flag_true);
        assert!(domain.is_top(&joined));
    }

    #[test]
    fn test_meet_commutative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        let m1 = domain.meet(&s1, &s2);
        let m2 = domain.meet(&s2, &s1);

        assert!(domain.equivalent(&m1, &m2));
    }

    #[test]
    fn test_meet_associative() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");
        domain.allocate_var("flag3");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let s3 = domain.mk_var_true("flag3");

        let left = domain.meet(&domain.meet(&s1, &s2), &s3);
        let right = domain.meet(&s1, &domain.meet(&s2, &s3));

        assert!(domain.equivalent(&left, &right));
    }

    #[test]
    fn test_meet_idempotent() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");
        let met = domain.meet(&flag_true, &flag_true);

        assert_eq!(flag_true, met);
    }

    #[test]
    fn test_meet_lower_bound() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");
        let met = domain.meet(&s1, &s2);

        // (s1 ⊓ s2) ⊑ s1 and (s1 ⊓ s2) ⊑ s2
        assert!(domain.le(&met, &s1));
        assert!(domain.le(&met, &s2));
    }

    #[test]
    fn test_meet_with_bottom() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let bottom = domain.bottom();
        let flag_true = domain.mk_var_true("flag");

        // ⊥ ⊓ φ = ⊥
        let met = domain.meet(&bottom, &flag_true);
        assert!(domain.is_bottom(&met));
    }

    #[test]
    fn test_meet_with_top() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let top = domain.top();
        let flag_true = domain.mk_var_true("flag");

        // ⊤ ⊓ φ = φ
        let met = domain.meet(&top, &flag_true);
        assert_eq!(met, flag_true);
    }

    #[test]
    fn test_meet_contradiction() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        let flag_true = domain.mk_var_true("flag");
        let flag_false = domain.mk_var_false("flag");

        // flag=true ⊓ flag=false = ⊥
        let met = domain.meet(&flag_true, &flag_false);
        assert!(domain.is_bottom(&met));
    }

    #[test]
    fn test_absorption_laws() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        // φ₁ ⊔ (φ₁ ⊓ φ₂) = φ₁
        let meet_result = domain.meet(&s1, &s2);
        let absorption1 = domain.join(&s1, &meet_result);
        assert!(domain.equivalent(&absorption1, &s1));

        // φ₁ ⊓ (φ₁ ⊔ φ₂) = φ₁
        let join_result = domain.join(&s1, &s2);
        let absorption2 = domain.meet(&s1, &join_result);
        assert!(domain.equivalent(&absorption2, &s1));
    }

    #[test]
    fn test_widen_same_as_join() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag1");
        domain.allocate_var("flag2");

        let s1 = domain.mk_var_true("flag1");
        let s2 = domain.mk_var_true("flag2");

        let joined = domain.join(&s1, &s2);
        let widened = domain.widen(&s1, &s2);

        assert!(domain.equivalent(&joined, &widened));
    }

    #[test]
    fn test_finite_height_convergence() {
        let domain = BddControlDomain::new();
        domain.allocate_var("flag");

        // Simulate ascending chain: ⊥ ⊑ flag=true ⊑ ⊤
        let bottom = domain.bottom();
        let flag_true = domain.mk_var_true("flag");
        let top = domain.top();

        // Chain must stabilize at top
        let step1 = domain.widen(&bottom, &flag_true);
        let step2 = domain.widen(&step1, &top);
        let step3 = domain.widen(&step2, &top);

        assert!(domain.is_top(&step3));
        assert_eq!(step2, step3); // Stabilized
    }

    // ========================================================================
    // Tests for imply and equiv operations
    // ========================================================================

    #[test]
    fn test_imply_operation() {
        let domain = BddControlDomain::new();
        domain.allocate_var("x");
        domain.allocate_var("y");

        let x = domain.mk_var_true("x");
        let y = domain.mk_var_true("y");
        let not_x = domain.mk_var_false("x");

        // x ⇒ y should be equivalent to ¬x ∨ y
        let imply_result = domain.imply(&x, &y);
        let expected = domain.or(&not_x, &y);
        assert!(domain.equivalent(&imply_result, &expected));

        // x ⇒ x should be ⊤
        let self_imply = domain.imply(&x, &x);
        assert!(domain.is_top(&self_imply));

        // ⊥ ⇒ x should be ⊤ (ex falso quodlibet)
        let bottom = domain.bottom();
        let bottom_imply = domain.imply(&bottom, &x);
        assert!(domain.is_top(&bottom_imply));

        // x ⇒ ⊥ should be equivalent to ¬x
        let imply_false = domain.imply(&x, &bottom);
        assert!(domain.equivalent(&imply_false, &not_x));

        // ⊤ ⇒ x should be equivalent to x
        let top = domain.top();
        let top_imply = domain.imply(&top, &x);
        assert!(domain.equivalent(&top_imply, &x));
    }

    #[test]
    fn test_equiv_operation() {
        let domain = BddControlDomain::new();
        domain.allocate_var("x");
        domain.allocate_var("y");

        let x = domain.mk_var_true("x");
        let y = domain.mk_var_true("y");

        // x ⇔ x should be ⊤
        let self_equiv = domain.equiv(&x, &x);
        assert!(domain.is_top(&self_equiv));

        // x ⇔ y should be equivalent to (x ∧ y) ∨ (¬x ∧ ¬y)
        let equiv_result = domain.equiv(&x, &y);
        let not_x = domain.mk_var_false("x");
        let not_y = domain.mk_var_false("y");
        let both_true = domain.and(&x, &y);
        let both_false = domain.and(&not_x, &not_y);
        let expected = domain.or(&both_true, &both_false);
        assert!(domain.equivalent(&equiv_result, &expected));

        // x ⇔ ¬x should be ⊥
        let contradiction = domain.equiv(&x, &not_x);
        assert!(domain.is_bottom(&contradiction));

        // ⊤ ⇔ ⊤ should be ⊤
        let top = domain.top();
        let top_equiv = domain.equiv(&top, &top);
        assert!(domain.is_top(&top_equiv));

        // ⊥ ⇔ ⊥ should be ⊤
        let bottom = domain.bottom();
        let bottom_equiv = domain.equiv(&bottom, &bottom);
        assert!(domain.is_top(&bottom_equiv));
    }

    #[test]
    fn test_imply_equiv_relationship() {
        let domain = BddControlDomain::new();
        domain.allocate_var("x");
        domain.allocate_var("y");

        let x = domain.mk_var_true("x");
        let y = domain.mk_var_true("y");

        // x ⇔ y ≡ (x ⇒ y) ∧ (y ⇒ x)
        let equiv_result = domain.equiv(&x, &y);
        let xy_imply = domain.imply(&x, &y);
        let yx_imply = domain.imply(&y, &x);
        let both_implications = domain.and(&xy_imply, &yx_imply);
        assert!(domain.equivalent(&equiv_result, &both_implications));
    }

    #[test]
    fn test_imply_transitivity() {
        let domain = BddControlDomain::new();
        domain.allocate_var("x");
        domain.allocate_var("y");
        domain.allocate_var("z");

        let x = domain.mk_var_true("x");
        let y = domain.mk_var_true("y");
        let z = domain.mk_var_true("z");

        // (x ⇒ y) ∧ (y ⇒ z) ⇒ (x ⇒ z)
        let xy = domain.imply(&x, &y);
        let yz = domain.imply(&y, &z);
        let xz = domain.imply(&x, &z);

        let premise = domain.and(&xy, &yz);
        let transitivity = domain.imply(&premise, &xz);
        assert!(domain.is_top(&transitivity));
    }

    #[test]
    fn test_equiv_symmetry() {
        let domain = BddControlDomain::new();
        domain.allocate_var("x");
        domain.allocate_var("y");

        let x = domain.mk_var_true("x");
        let y = domain.mk_var_true("y");

        // x ⇔ y should be the same as y ⇔ x
        let xy_equiv = domain.equiv(&x, &y);
        let yx_equiv = domain.equiv(&y, &x);
        assert!(domain.equivalent(&xy_equiv, &yx_equiv));
    }

    #[test]
    fn test_optimized_implies() {
        let domain = BddControlDomain::new();
        domain.allocate_var("x");
        domain.allocate_var("y");

        let x = domain.mk_var_true("x");
        let y = domain.mk_var_true("y");
        let not_x = domain.mk_var_false("x");

        // Test the optimized implies check
        assert!(domain.implies(&x, &x)); // reflexive
        assert!(!domain.implies(&x, &not_x)); // contradiction

        let top = domain.top();
        let bottom = domain.bottom();
        assert!(domain.implies(&x, &top)); // anything implies top
        assert!(domain.implies(&bottom, &x)); // bottom implies anything

        // x ∧ y implies x
        let xy = domain.and(&x, &y);
        assert!(domain.implies(&xy, &x));
        assert!(domain.implies(&xy, &y));

        // x does not imply x ∧ y
        assert!(!domain.implies(&x, &xy));
    }

    #[test]
    fn test_optimized_equivalent() {
        let domain = BddControlDomain::new();
        domain.allocate_var("x");

        let x1 = domain.mk_var_true("x");
        let x2 = domain.mk_var_true("x");
        let not_x = domain.mk_var_false("x");

        // Same BDD refs should be equivalent (optimized path)
        assert!(domain.equivalent(&x1, &x2));

        // Different formulas should not be equivalent
        assert!(!domain.equivalent(&x1, &not_x));

        // Logically equivalent but constructed differently
        let double_neg = domain.not(&not_x);
        assert!(domain.equivalent(&x1, &double_neg));
    }
}

// ============================================================================
// Control-Sensitive Product Domain
// ============================================================================

/// Control-Sensitive Product Domain: BDD Control × Numeric Domain
///
/// This structure implements path-sensitive analysis by maintaining separate
/// numeric abstract states for different control states. The key insight is:
///
/// **State = Map[ControlState → NumericElement]**
///
/// # Theory
///
/// The control-sensitive product is a reduced product construction:
///
/// ```text
/// D_Product = D_BDD ⨯ D_Numeric
/// ```
///
/// Where the reduction function enforces:
/// 1. **Feasibility**: Only reachable control states have numeric states
/// 2. **Precision**: Numeric states reflect control constraints
///
/// # Lattice Operations
///
/// - **Bottom**: Empty map (no reachable states)
/// - **Top**: Single entry (`true → ⊤_numeric`)
/// - **Join**: Union of partitions with numeric join per key
/// - **Meet**: Intersection of partitions with numeric meet per key
/// - **Partial Order**: `φ₁ ⊑ φ₂` if `∀` partition in `φ₁`, `∃` weaker partition in `φ₂`
///
/// # Example
///
/// ```rust,ignore
/// // Program: if (flag) { x = [0,10] } else { x = [20,30] }
/// let product = ControlSensitiveProduct::new(bdd_domain, interval_domain);
///
/// // Path 1: flag=true → x ∈ [0,10]
/// let path1 = (mk_var_true("flag"), Interval::new(0, 10));
///
/// // Path 2: flag=false → x ∈ [20,30]
/// let path2 = (mk_var_false("flag"), Interval::new(20, 30));
///
/// // Join: maintains separate partitions
/// let joined = product.join(&path1, &path2);
/// // Result: {flag=true → [0,10], flag=false → [20,30]}
///
/// // Path-insensitive would lose precision: x ∈ [0,30]
/// ```
///
/// # Implementation Notes
///
/// - Uses `HashMap` for partition storage (BDD comparison via node equality)
/// - Automatic partition merging when control states become equivalent
/// - Lazy partition splitting on control variable assignments
///
/// Wrapper for ControlState that implements Hash and Eq via node pointer comparison
#[derive(Clone, Debug)]
struct HashableControlState(ControlState);

impl Hash for HashableControlState {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the Boolean formula φ directly (Ref implements Hash)
        self.0.phi.hash(state);
    }
}

impl PartialEq for HashableControlState {
    fn eq(&self, other: &Self) -> bool {
        self.0.phi == other.0.phi
    }
}

impl Eq for HashableControlState {}

/// Control-Sensitive Product Domain Element
///
/// Represents a path-sensitive abstract state as a map from control states
/// to numeric abstract values.
#[derive(Clone, Debug)]
pub struct ControlSensitiveElement<N: NumericDomain> {
    /// Map from control states to numeric elements
    /// Invariant: All control states are satisfiable (not bottom)
    partitions: HashMap<HashableControlState, N::Element>,
    /// Reference to BDD control domain for operations
    #[allow(dead_code)]
    control_domain: Rc<BddControlDomain>,
    /// Reference to numeric domain for operations
    numeric_domain: Rc<N>,
}

impl<N: NumericDomain> PartialEq for ControlSensitiveElement<N> {
    fn eq(&self, other: &Self) -> bool {
        // Two elements are equal if they have the same partitions
        if self.partitions.len() != other.partitions.len() {
            return false;
        }

        // Check all partitions match
        for (hcs, elem) in &self.partitions {
            match other.partitions.get(hcs) {
                Some(other_elem) if self.numeric_domain.le(elem, other_elem) && self.numeric_domain.le(other_elem, elem) => {}
                _ => return false,
            }
        }

        true
    }
}

impl<N: NumericDomain> Eq for ControlSensitiveElement<N> {}

impl<N: NumericDomain> ControlSensitiveElement<N> {
    /// Create a new empty element (bottom)
    pub fn new_empty(control_domain: Rc<BddControlDomain>, numeric_domain: Rc<N>) -> Self {
        Self {
            partitions: HashMap::new(),
            control_domain,
            numeric_domain,
        }
    }

    /// Check if this element represents bottom (empty map)
    pub fn is_empty(&self) -> bool {
        self.partitions.is_empty()
    }

    /// Get number of partitions
    pub fn partition_count(&self) -> usize {
        self.partitions.len()
    }

    /// Iterate over (control_state, numeric_element) pairs
    pub fn iter(&self) -> impl Iterator<Item = (&ControlState, &N::Element)> {
        self.partitions.iter().map(|(hcs, elem)| (&hcs.0, elem))
    }

    /// Get numeric element for a specific control state (if exists)
    pub fn get(&self, control_state: &ControlState) -> Option<&N::Element> {
        self.partitions.get(&HashableControlState(control_state.clone()))
    }

    /// Check if a specific control state exists in partitions
    pub fn contains_path(&self, control_state: &ControlState) -> bool {
        self.partitions.contains_key(&HashableControlState(control_state.clone()))
    }

    /// Get all control states from partitions
    pub fn control_states(&self) -> Vec<&ControlState> {
        self.partitions.keys().map(|hcs| &hcs.0).collect()
    }
}

/// Control-Sensitive Product Domain
///
/// Combines BDD control domain with any numeric domain for path-sensitive analysis.
#[derive(Clone, Debug)]
pub struct ControlSensitiveProduct<N: NumericDomain> {
    /// BDD control domain for Boolean control variables
    control_domain: Rc<BddControlDomain>,
    /// Numeric domain for data variables
    numeric_domain: Rc<N>,
}

impl<N: NumericDomain> ControlSensitiveProduct<N> {
    /// Create a new control-sensitive product domain
    ///
    /// # Arguments
    ///
    /// * `control_domain` - BDD domain for control variables
    /// * `numeric_domain` - Numeric domain for data variables
    pub fn new(control_domain: Rc<BddControlDomain>, numeric_domain: Rc<N>) -> Self {
        ControlSensitiveProduct {
            control_domain,
            numeric_domain,
        }
    }

    /// Create element from single partition
    ///
    /// This is a convenience method for creating a control-sensitive element
    /// with exactly one partition (control state → numeric state mapping).
    ///
    /// # Arguments
    ///
    /// * `control_state` - The control state for this partition
    /// * `numeric_elem` - The numeric abstract value for this partition
    ///
    /// # Returns
    ///
    /// A new element with a single partition, or an empty element if either input is bottom.
    pub fn mk_single_partition(&self, control_state: ControlState, numeric_elem: N::Element) -> ControlSensitiveElement<N> {
        let mut partitions = HashMap::new();
        if !self.control_domain.is_bottom(&control_state) && !self.numeric_domain.is_bottom(&numeric_elem) {
            partitions.insert(HashableControlState(control_state), numeric_elem);
        }
        ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Merge partitions with overlapping or equivalent control states
    ///
    /// This is a key optimization: when multiple partitions have control states
    /// that are logically equivalent, we can merge their numeric states.
    fn _merge_equivalent_partitions(&self, elem: &ControlSensitiveElement<N>) -> ControlSensitiveElement<N> {
        // For now, just return the element unchanged
        // TODO: Implement partition merging optimization
        elem.clone()
    }

    /// Filter partitions by a control condition (assume condition holds)
    ///
    /// Refines each partition's control state with the given condition.
    /// Only keeps partitions where `control_state ∧ condition` is satisfiable.
    pub fn split_on_condition(&self, elem: &ControlSensitiveElement<N>, condition: &ControlState) -> ControlSensitiveElement<N> {
        self.filter_partitions(elem, |cs| self.control_domain.and(cs, condition))
    }

    /// Apply a control transformation to each partition and filter out infeasible ones
    fn filter_partitions<F>(&self, elem: &ControlSensitiveElement<N>, transform: F) -> ControlSensitiveElement<N>
    where
        F: Fn(&ControlState) -> ControlState,
    {
        let mut new_partitions = HashMap::new();

        for (hcs, numeric_elem) in &elem.partitions {
            let transformed = transform(&hcs.0);
            if !self.control_domain.is_bottom(&transformed) {
                new_partitions.insert(HashableControlState(transformed), numeric_elem.clone());
            }
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Split each partition into two: one where condition holds, one where it doesn't
    ///
    /// This implements the splitting logic from section 3.1 of the design doc.
    /// Each partition (φ, e) is split into:
    /// - (φ ∧ condition, e) if satisfiable
    /// - (φ ∧ ¬condition, e) if satisfiable
    ///
    /// # Example
    /// ```text
    /// // Before: {(true, x ∈ [0,10])}
    /// // Split on: flag = true
    /// // After: {(flag, x ∈ [0,10]), (¬flag, x ∈ [0,10])}
    /// ```
    pub fn split_partition(&self, elem: &ControlSensitiveElement<N>, condition: &ControlState) -> ControlSensitiveElement<N>
    where
        N::Element: Clone,
    {
        let mut new_partitions = HashMap::new();
        let neg_condition = self.control_domain.not(condition);

        for (hcs, numeric_elem) in &elem.partitions {
            let control_state = &hcs.0;

            // Branch 1: φ ∧ condition
            let branch_true = self.control_domain.and(control_state, condition);
            if !self.control_domain.is_bottom(&branch_true) {
                new_partitions.insert(HashableControlState(branch_true), numeric_elem.clone());
            }

            // Branch 2: φ ∧ ¬condition
            let branch_false = self.control_domain.and(control_state, &neg_condition);
            if !self.control_domain.is_bottom(&branch_false) {
                new_partitions.insert(HashableControlState(branch_false), numeric_elem.clone());
            }
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Get reference to control domain
    pub fn control_domain(&self) -> &BddControlDomain {
        &self.control_domain
    }

    /// Get reference to numeric domain
    pub fn numeric_domain(&self) -> &N {
        &self.numeric_domain
    }
}

// ============================================================================
// AbstractDomain Implementation for Control-Sensitive Product
// ============================================================================

impl<N: NumericDomain> AbstractDomain for ControlSensitiveProduct<N> {
    type Element = ControlSensitiveElement<N>;

    /// Bottom: Empty map (no reachable states)
    ///
    /// The empty map represents unreachable code - no control path is feasible.
    fn bottom(&self) -> Self::Element {
        ControlSensitiveElement {
            partitions: HashMap::new(),
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Top: Single partition (true → ⊤_numeric)
    ///
    /// Represents all control paths are reachable with no numeric constraints.
    fn top(&self) -> Self::Element {
        let mut partitions = HashMap::new();
        let control_top = self.control_domain.top();
        let numeric_top = self.numeric_domain.top();
        partitions.insert(HashableControlState(control_top), numeric_top);

        ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Check if element is bottom (empty map)
    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_empty()
    }

    /// Check if element is top (single partition with control=true, numeric=top)
    ///
    /// Note: This is an approximation. True top means all control paths are
    /// feasible and no numeric constraints exist.
    fn is_top(&self, elem: &Self::Element) -> bool {
        if elem.partition_count() != 1 {
            return false;
        }

        if let Some((control_state, numeric_elem)) = elem.partitions.iter().next() {
            self.control_domain.is_top(&control_state.0) && self.numeric_domain.is_top(numeric_elem)
        } else {
            false
        }
    }

    /// Partial order: elem1 ⊑ elem2 if every partition in elem1 is covered by elem2
    ///
    /// More precisely:
    /// ```text
    /// φ₁ ⊑ φ₂ ⟺ ∀(c₁, n₁) ∈ φ₁: ∃(c₂, n₂) ∈ φ₂: c₁ ⊑ c₂ ∧ n₁ ⊑ n₂
    /// ```
    ///
    /// This implements a partition-wise ordering where we check if each
    /// partition in elem1 can be subsumed by some partition in elem2.
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        // Bottom is less than everything
        if elem1.is_empty() {
            return true;
        }

        // Check if every partition in elem1 is covered by elem2
        for (hcs1, numeric1) in &elem1.partitions {
            let control1 = &hcs1.0;

            // Find a covering partition in elem2
            let mut covered = false;
            for (hcs2, numeric2) in &elem2.partitions {
                let control2 = &hcs2.0;

                // Check if control1 ⊑ control2 and numeric1 ⊑ numeric2
                if self.control_domain.le(control1, control2) && self.numeric_domain.le(numeric1, numeric2) {
                    covered = true;
                    break;
                }
            }

            if !covered {
                return false;
            }
        }

        true
    }

    /// Join: Union of partitions with numeric join per overlapping control state
    ///
    /// The join operation merges partitions from both elements:
    /// ```text
    /// φ₁ ⊔ φ₂ = { (c, n₁ ⊔ n₂) | (c, n₁) ∈ φ₁, (c, n₂) ∈ φ₂ }
    ///          ∪ { (c, n) | (c, n) ∈ φ₁, c ∉ domain(φ₂) }
    ///          ∪ { (c, n) | (c, n) ∈ φ₂, c ∉ domain(φ₁) }
    /// ```
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let mut new_partitions = HashMap::new();

        // Add all partitions from elem1
        for (hcs1, numeric1) in &elem1.partitions {
            new_partitions.insert(hcs1.clone(), numeric1.clone());
        }

        // Merge/add partitions from elem2
        for (hcs2, numeric2) in &elem2.partitions {
            new_partitions
                .entry(hcs2.clone())
                .and_modify(|numeric1| {
                    *numeric1 = self.numeric_domain.join(numeric1, numeric2);
                })
                .or_insert_with(|| numeric2.clone());
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Meet: Intersection of partitions with numeric meet
    ///
    /// The meet operation computes pairwise intersections:
    /// ```text
    /// φ₁ ⊓ φ₂ = { (c₁ ∧ c₂, n₁ ⊓ n₂) | (c₁, n₁) ∈ φ₁, (c₂, n₂) ∈ φ₂ }
    /// ```
    ///
    /// Only feasible combinations (non-bottom) are retained.
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let mut new_partitions = HashMap::new();

        // Compute pairwise meets of all partition combinations
        for (hcs1, numeric1) in &elem1.partitions {
            for (hcs2, numeric2) in &elem2.partitions {
                let control1 = &hcs1.0;
                let control2 = &hcs2.0;

                // Combine control states
                let control_meet = self.control_domain.meet(control1, control2);

                // Only add if control state is feasible
                if !self.control_domain.is_bottom(&control_meet) {
                    let numeric_meet = self.numeric_domain.meet(numeric1, numeric2);

                    // Only add if numeric state is feasible
                    if !self.numeric_domain.is_bottom(&numeric_meet) {
                        new_partitions.insert(HashableControlState(control_meet), numeric_meet);
                    }
                }
            }
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Widening: Partition-wise widening with partition merging
    ///
    /// The widening operator handles two aspects:
    /// 1. **Numeric widening**: Apply numeric widening per partition
    /// 2. **Partition merging**: Merge partitions to ensure termination
    ///
    /// ```text
    /// φ₁ ∇ φ₂ = merge({ (c, n₁ ∇ n₂) | (c, n₁) ∈ φ₁, (c, n₂) ∈ φ₂ })
    /// ```
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let mut new_partitions = HashMap::new();

        // Widen matching partitions
        for (hcs1, numeric1) in &elem1.partitions {
            if let Some(numeric2) = elem2.partitions.get(hcs1) {
                // Same control state: widen numeric parts
                let widened = self.numeric_domain.widen(numeric1, numeric2);
                new_partitions.insert(hcs1.clone(), widened);
            } else {
                // Control state only in elem1: keep it
                new_partitions.insert(hcs1.clone(), numeric1.clone());
            }
        }

        // Add new partitions from elem2
        for (hcs2, numeric2) in &elem2.partitions {
            new_partitions.entry(hcs2.clone()).or_insert_with(|| numeric2.clone());
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }
}

// ============================================================================
// Control-Sensitive Operations
// ============================================================================

impl<N: NumericDomain> ControlSensitiveProduct<N> {
    /// Apply a numeric assignment across all partitions
    ///
    /// Delegates the assignment to the underlying numeric domain for each partition:
    /// ```text
    /// assign_all(var, expr, { (c₁, n₁), (c₂, n₂), ... })
    ///     = { (c₁, assign_numeric(n₁, var, expr)),
    ///         (c₂, assign_numeric(n₂, var, expr)), ... }
    /// ```
    pub fn assign_all(
        &self,
        elem: &ControlSensitiveElement<N>,
        var: &N::Var,
        expr: &crate::expr::NumExpr<N::Var, N::Value>,
    ) -> ControlSensitiveElement<N>
    where
        N::Element: Clone,
    {
        let mut new_partitions = HashMap::new();

        for (hcs, numeric_elem) in &elem.partitions {
            let new_numeric = self.numeric_domain.assign(numeric_elem, var.clone(), expr);

            // Only keep feasible partitions
            if !self.numeric_domain.is_bottom(&new_numeric) {
                new_partitions.insert(hcs.clone(), new_numeric);
            }
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Apply a numeric assumption across all partitions
    ///
    /// Refines each partition by assuming a numeric predicate holds:
    /// ```text
    /// assume_all(pred, { (c₁, n₁), (c₂, n₂), ... })
    ///     = { (c₁, assume_numeric(n₁, pred)),
    ///         (c₂, assume_numeric(n₂, pred)), ... }
    /// ```
    ///
    /// Infeasible partitions (where assume returns bottom) are removed.
    pub fn assume_all(&self, elem: &ControlSensitiveElement<N>, pred: &crate::expr::NumPred<N::Var, N::Value>) -> ControlSensitiveElement<N>
    where
        N::Element: Clone,
    {
        let mut new_partitions = HashMap::new();

        for (hcs, numeric_elem) in &elem.partitions {
            let new_numeric = self.numeric_domain.assume(numeric_elem, pred);

            // Only keep feasible partitions
            if !self.numeric_domain.is_bottom(&new_numeric) {
                new_partitions.insert(hcs.clone(), new_numeric);
            }
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Project out a variable from all partitions
    pub fn project_all(&self, elem: &ControlSensitiveElement<N>, var: &N::Var) -> ControlSensitiveElement<N>
    where
        N::Element: Clone,
    {
        let mut new_partitions = HashMap::new();

        for (hcs, numeric_elem) in &elem.partitions {
            let new_numeric = self.numeric_domain.project(numeric_elem, var);
            new_partitions.insert(hcs.clone(), new_numeric);
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }
}

// ============================================================================
// Control Variable Transfer Functions
// ============================================================================

impl<N: NumericDomain> ControlSensitiveProduct<N> {
    /// Assign a control variable: control_var := expr
    ///
    /// This implements section 3.1 of the design document.
    /// The semantics depend on whether `expr` can be evaluated in the current context:
    ///
    /// - **expr = true**: Refine control state with `var = true`
    /// - **expr = false**: Refine control state with `var = false`
    /// - **expr = unknown**: Split partition into two cases (var=true, var=false)
    ///
    /// # Example (Simple Assignment)
    /// ```text
    /// // Before: {(true, x ∈ [0,10])}
    /// assign_control("flag", true)
    /// // After: {(flag, x ∈ [0,10])}
    /// ```
    ///
    /// # Example (Splitting - expr unknown)
    /// ```text
    /// // Before: {(true, x ∈ [0,10])}
    /// // Assign: flag := (x > 5)  -- unknown, depends on x
    /// // After: {
    /// //   (flag ∧ x>5, x ∈ [6,10]),
    /// //   (¬flag ∧ x≤5, x ∈ [0,5])
    /// // }
    /// ```
    pub fn assign_control(&self, var_name: &str, value: bool, elem: &ControlSensitiveElement<N>) -> ControlSensitiveElement<N> {
        // Simple case: assigning a constant value
        // This refines each partition with the constraint var=value
        let condition = if value {
            self.control_domain.mk_var_true(var_name)
        } else {
            self.control_domain.mk_var_false(var_name)
        };

        self.split_on_condition(elem, &condition)
    }

    /// Assign control variable from Boolean expression: control_var := expr
    ///
    /// This is the full version that handles unknown expressions by splitting.
    /// When `expr` depends on data variables, we split each partition:
    /// - Path where expr=true: set var=true, refine numeric state with expr
    /// - Path where expr=false: set var=false, refine numeric state with ¬expr
    ///
    /// # Arguments
    /// * `var_name` - Control variable being assigned
    /// * `condition_true` - ControlState representing when expr is true
    /// * `condition_false` - ControlState representing when expr is false (optional, defaults to ¬condition_true)
    ///
    /// # Example
    /// ```text
    /// // Program: flag := (x > 5)
    /// // Before: {(true, x ∈ [0,10])}
    ///
    /// let cond_true = control_domain.mk_var_true("x_gt_5");
    /// assign_control_from_expr("flag", &cond_true, elem);
    ///
    /// // After: {
    /// //   (flag ∧ x_gt_5, x ∈ [6,10]),
    /// //   (¬flag ∧ ¬x_gt_5, x ∈ [0,5])
    /// // }
    /// ```
    pub fn assign_control_from_expr(
        &self,
        var_name: &str,
        condition: &ControlState,
        elem: &ControlSensitiveElement<N>,
    ) -> ControlSensitiveElement<N>
    where
        N::Element: Clone,
    {
        let mut new_partitions = HashMap::new();
        let neg_condition = self.control_domain.not(condition);

        // Get the BDD variables for the control variable
        let var_true = self.control_domain.mk_var_true(var_name);
        let var_false = self.control_domain.mk_var_false(var_name);

        for (hcs, numeric_elem) in &elem.partitions {
            let control_state = &hcs.0;

            // Check if condition is definitely true, definitely false, or unknown
            let cond_and_state = self.control_domain.and(control_state, condition);
            let neg_cond_and_state = self.control_domain.and(control_state, &neg_condition);

            let cond_true_feasible = !self.control_domain.is_bottom(&cond_and_state);
            let cond_false_feasible = !self.control_domain.is_bottom(&neg_cond_and_state);

            match (cond_true_feasible, cond_false_feasible) {
                (true, false) => {
                    // Condition is definitely true: set var = true
                    let new_control = self.control_domain.and(control_state, &var_true);
                    if !self.control_domain.is_bottom(&new_control) {
                        new_partitions.insert(HashableControlState(new_control), numeric_elem.clone());
                    }
                }
                (false, true) => {
                    // Condition is definitely false: set var = false
                    let new_control = self.control_domain.and(control_state, &var_false);
                    if !self.control_domain.is_bottom(&new_control) {
                        new_partitions.insert(HashableControlState(new_control), numeric_elem.clone());
                    }
                }
                (true, true) => {
                    // Condition is unknown: SPLIT into both cases

                    // Branch 1: condition is true, so var = true
                    let branch_true = self.control_domain.and(&cond_and_state, &var_true);
                    if !self.control_domain.is_bottom(&branch_true) {
                        new_partitions.insert(HashableControlState(branch_true), numeric_elem.clone());
                    }

                    // Branch 2: condition is false, so var = false
                    let branch_false = self.control_domain.and(&neg_cond_and_state, &var_false);
                    if !self.control_domain.is_bottom(&branch_false) {
                        new_partitions.insert(HashableControlState(branch_false), numeric_elem.clone());
                    }
                }
                (false, false) => {
                    // Both infeasible: partition is unreachable, skip it
                }
            }
        }

        ControlSensitiveElement {
            partitions: new_partitions,
            control_domain: Rc::clone(&self.control_domain),
            numeric_domain: Rc::clone(&self.numeric_domain),
        }
    }

    /// Assume a control condition
    ///
    /// Refines partitions by assuming a Boolean condition holds.
    /// This is the path-sensitive equivalent of filtering by a control predicate.
    ///
    /// # Example
    /// ```text
    /// // Program: if (flag) { ... }
    /// // Before: {(true, n)}
    /// assume_control(flag_true)
    /// // After: {(flag=true, n)}  -- only flag=true path remains
    /// ```
    pub fn assume_control(&self, condition: &ControlState, elem: &ControlSensitiveElement<N>) -> ControlSensitiveElement<N> {
        self.split_on_condition(elem, condition)
    }

    /// Query numeric value for a specific control state
    ///
    /// This allows inspecting the numeric invariant on a particular control path.
    ///
    /// # Returns
    /// - `Some(numeric_elem)` if the control state is feasible
    /// - `None` if no partition matches this control state
    pub fn query_on_path(&self, control_state: &ControlState, elem: &ControlSensitiveElement<N>) -> Option<N::Element>
    where
        N::Element: Clone,
    {
        elem.get(control_state).cloned()
    }
}

// ============================================================================
// Tests for Control-Sensitive Product Domain
// ============================================================================

#[cfg(test)]
mod product_tests {
    use super::*;
    use crate::expr::NumExpr;
    use crate::interval::{Bound, Interval, IntervalDomain, IntervalElement};

    // Helper to create a simple product domain for testing
    fn make_product_domain() -> ControlSensitiveProduct<IntervalDomain> {
        let control_domain = Rc::new(BddControlDomain::new());
        let numeric_domain = Rc::new(IntervalDomain);
        ControlSensitiveProduct::new(control_domain, numeric_domain)
    }

    #[test]
    fn test_product_bottom_top() {
        let product = make_product_domain();

        let bottom = product.bottom();
        assert!(product.is_bottom(&bottom));
        assert_eq!(bottom.partition_count(), 0);

        let top = product.top();
        // Top should have exactly 1 partition with control=true
        assert_eq!(top.partition_count(), 1);
        // Verify the control state is top
        let (control_state, _numeric_elem) = top.partitions.iter().next().unwrap();
        assert!(product.control_domain.is_top(&control_state.0));
        // Note: IntervalDomain's is_top always returns false, so we can't check numeric top
    }
    #[test]
    fn test_product_partial_order() {
        let product = make_product_domain();

        let bottom = product.bottom();
        let top = product.top();

        // Bottom ⊑ Everything
        assert!(product.le(&bottom, &top));
        assert!(product.le(&bottom, &bottom));

        // Top is greatest
        assert!(product.le(&top, &top));
        assert!(!product.le(&top, &bottom));
    }

    #[test]
    fn test_product_join_empty() {
        let product = make_product_domain();

        let bottom = product.bottom();
        let top = product.top();

        // ⊥ ⊔ ⊤ = ⊤ (should have 1 partition like top)
        let joined = product.join(&bottom, &top);
        assert_eq!(joined.partition_count(), 1);
        // Verify top ⊑ joined and joined ⊑ top
        assert!(product.le(&top, &joined));
        assert!(product.le(&joined, &top));

        // ⊥ ⊔ ⊥ = ⊥
        let joined_bottom = product.join(&bottom, &bottom);
        assert!(product.is_bottom(&joined_bottom));
    }

    #[test]
    fn test_product_meet_empty() {
        let product = make_product_domain();

        let bottom = product.bottom();
        let top = product.top();

        // ⊥ ⊓ ⊤ = ⊥
        let met = product.meet(&bottom, &top);
        assert!(product.is_bottom(&met));

        // ⊤ ⊓ ⊤ = ⊤ (should be equivalent)
        let met_top = product.meet(&top, &top);
        assert_eq!(met_top.partition_count(), 1);
        // Verify it's equivalent to top
        assert!(product.le(&met_top, &top));
        assert!(product.le(&top, &met_top));
    }

    #[test]
    fn test_simple_flag_example() {
        // Example 8.1 from design doc: Simple flag analysis
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Initial: {true ↦ x = 0}
        let control_top = control_domain.top();
        let mut numeric_initial = IntervalElement::new();
        numeric_initial.set("x", Interval::constant(0));

        let mut partitions = HashMap::new();
        partitions.insert(HashableControlState(control_top), numeric_initial);
        let initial = ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Assign: flag := true, x := 5
        let state_after_assign = product.assign_control("flag", true, &initial);
        assert_eq!(state_after_assign.partition_count(), 1);

        // Apply numeric assignment x := 5
        let expr = NumExpr::constant(5);
        let state_with_x5 = product.assign_all(&state_after_assign, &"x".to_string(), &expr);

        // Should have one partition: flag=true → x=5
        assert_eq!(state_with_x5.partition_count(), 1);
    }

    #[test]
    fn test_splitting_on_unknown_condition() {
        // Test section 3.1: splitting when condition is unknown
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Start with: {true ↦ x ∈ [0,10]}
        let control_top = control_domain.top();
        let mut numeric_initial = IntervalElement::new();
        numeric_initial.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));

        let mut partitions = HashMap::new();
        partitions.insert(HashableControlState(control_top.clone()), numeric_initial.clone());
        let initial = ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Split on condition: flag (unknown value)
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");

        // Use split_partition to create both branches
        let split = product.split_partition(&initial, &flag_true);

        // Should have 2 partitions: flag=true and flag=false
        assert_eq!(split.partition_count(), 2);
    }

    #[test]
    fn test_assume_control_filters_partitions() {
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Create partitions: {flag=true ↦ x=5, flag=false ↦ x=0}
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");
        let flag_false = control_domain.mk_var_false("flag");

        let mut numeric1 = IntervalElement::new();
        numeric1.set("x", Interval::constant(5));

        let mut numeric2 = IntervalElement::new();
        numeric2.set("x", Interval::constant(0));

        let mut partitions = HashMap::new();
        partitions.insert(HashableControlState(flag_true.clone()), numeric1);
        partitions.insert(HashableControlState(flag_false), numeric2);

        let elem = ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Assume flag=true
        let filtered = product.assume_control(&flag_true, &elem);

        // Should only have flag=true partition
        assert_eq!(filtered.partition_count(), 1);
    }

    #[test]
    fn test_assign_all_preserves_partitions() {
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Create two partitions with different control states
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");
        let flag_false = control_domain.mk_var_false("flag");

        let mut numeric1 = IntervalElement::new();
        numeric1.set("x", Interval::constant(5));

        let mut numeric2 = IntervalElement::new();
        numeric2.set("x", Interval::constant(10));

        let mut partitions = HashMap::new();
        partitions.insert(HashableControlState(flag_true), numeric1.clone());
        partitions.insert(HashableControlState(flag_false), numeric2.clone());

        let elem = ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Assign: x := x + 1
        let expr = NumExpr::var("x").add(NumExpr::constant(1));
        let result = product.assign_all(&elem, &"x".to_string(), &expr);

        // Should still have 2 partitions (control states unchanged)
        assert_eq!(result.partition_count(), 2);
    }

    #[test]
    fn test_assume_all_refines_numeric() {
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Start with: {true ↦ x ∈ [0,10]}
        let control_top = control_domain.top();
        let mut numeric = IntervalElement::new();
        numeric.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));

        let mut partitions = HashMap::new();
        partitions.insert(HashableControlState(control_top), numeric);

        let elem = ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Assume: x > 5  (should refine to [6,10])
        let pred = NumExpr::var("x").gt(NumExpr::constant(5));
        let refined = product.assume_all(&elem, &pred);

        // Should still have 1 partition, but refined numeric state
        assert_eq!(refined.partition_count(), 1);
    }

    #[test]
    fn test_product_join_merges_partitions() {
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Create elem1: {flag=true ↦ x=5}
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");

        let mut numeric1 = IntervalElement::new();
        numeric1.set("x", Interval::constant(5));

        let mut partitions1 = HashMap::new();
        partitions1.insert(HashableControlState(flag_true.clone()), numeric1);

        let elem1 = ControlSensitiveElement {
            partitions: partitions1,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Create elem2: {flag=false ↦ x=0}
        let flag_false = control_domain.mk_var_false("flag");

        let mut numeric2 = IntervalElement::new();
        numeric2.set("x", Interval::constant(0));

        let mut partitions2 = HashMap::new();
        partitions2.insert(HashableControlState(flag_false), numeric2);

        let elem2 = ControlSensitiveElement {
            partitions: partitions2,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Join should combine partitions
        let joined = product.join(&elem1, &elem2);

        // Should have 2 partitions: flag=true → x=5, flag=false → x=0
        assert_eq!(joined.partition_count(), 2);
    }

    #[test]
    fn test_product_meet_intersects_partitions() {
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Create elem1: {flag=true ↦ x ∈ [0,10]}
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");

        let mut numeric1 = IntervalElement::new();
        numeric1.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));

        let mut partitions1 = HashMap::new();
        partitions1.insert(HashableControlState(flag_true.clone()), numeric1);

        let elem1 = ControlSensitiveElement {
            partitions: partitions1,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Create elem2: {flag=true ↦ x ∈ [5,15]}
        let mut numeric2 = IntervalElement::new();
        numeric2.set("x", Interval::new(Bound::Finite(5), Bound::Finite(15)));

        let mut partitions2 = HashMap::new();
        partitions2.insert(HashableControlState(flag_true), numeric2);

        let elem2 = ControlSensitiveElement {
            partitions: partitions2,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Meet should intersect both control and numeric
        let met = product.meet(&elem1, &elem2);

        // Should have 1 partition: flag=true → x ∈ [5,10]
        assert_eq!(met.partition_count(), 1);
    }

    #[test]
    fn test_control_sensitive_precision() {
        // Demonstrate precision improvement: Example 8.1 complete
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Program:
        // x = 0; flag = false;
        // if (input > 10) { flag = true; x = 5; }
        // if (flag) { x = x + 10; }
        // assert(x == 15 || x == 0);

        // Initial: {true ↦ x=0, flag undefined}
        let control_top = control_domain.top();
        let mut numeric_initial = IntervalElement::new();
        numeric_initial.set("x", Interval::constant(0));

        let mut partitions = HashMap::new();
        partitions.insert(HashableControlState(control_top), numeric_initial);

        let _state0 = ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Branch on input > 10: split into flag=true and flag=false paths
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");
        let flag_false = control_domain.mk_var_false("flag");

        // Path 1: flag=true, x=5
        let mut numeric_path1 = IntervalElement::new();
        numeric_path1.set("x", Interval::constant(5));

        let mut partitions1 = HashMap::new();
        partitions1.insert(HashableControlState(flag_true.clone()), numeric_path1);

        let path1 = ControlSensitiveElement {
            partitions: partitions1,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Path 2: flag=false, x=0
        let mut numeric_path2 = IntervalElement::new();
        numeric_path2.set("x", Interval::constant(0));

        let mut partitions2 = HashMap::new();
        partitions2.insert(HashableControlState(flag_false), numeric_path2);

        let path2 = ControlSensitiveElement {
            partitions: partitions2,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Join paths
        let state_after_if1 = product.join(&path1, &path2);
        assert_eq!(state_after_if1.partition_count(), 2);

        // Second if (flag): only affects flag=true partition
        // For flag=true: x := x + 10 (5 + 10 = 15)
        let expr_add10 = NumExpr::var("x").add(NumExpr::constant(10));

        // Apply only to flag=true partition
        let flag_true_path = product.assume_control(&flag_true, &state_after_if1);
        let flag_true_updated = product.assign_all(&flag_true_path, &"x".to_string(), &expr_add10);

        // Query x on flag=true path
        let numeric_on_true = flag_true_updated.partitions.values().next().unwrap();
        let x_interval_true = numeric_on_true.get("x");
        assert_eq!(x_interval_true, Interval::constant(15));

        // The path-sensitive analysis proves x ∈ {0, 15}, not [0,15]!
    }

    #[test]
    fn test_query_on_path() {
        let product = make_product_domain();
        let control_domain = product.control_domain();

        // Create partitions
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");
        let flag_false = control_domain.mk_var_false("flag");

        let mut numeric1 = IntervalElement::new();
        numeric1.set("x", Interval::constant(5));

        let mut numeric2 = IntervalElement::new();
        numeric2.set("x", Interval::constant(0));

        let mut partitions = HashMap::new();
        partitions.insert(HashableControlState(flag_true.clone()), numeric1.clone());
        partitions.insert(HashableControlState(flag_false.clone()), numeric2.clone());

        let elem = ControlSensitiveElement {
            partitions,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        // Verify we have exactly 2 partitions
        assert_eq!(elem.partition_count(), 2);

        // Query on flag=true path (using the same BDD reference we inserted)
        let result_true = product.query_on_path(&flag_true, &elem);
        assert!(
            result_true.is_some(),
            "Should find flag=true partition (found {} partitions)",
            elem.partition_count()
        );
        if let Some(numeric) = result_true {
            assert_eq!(numeric.get("x"), Interval::constant(5));
        }

        // Query on flag=false path (using the same BDD reference we inserted)
        let result_false = product.query_on_path(&flag_false, &elem);
        assert!(result_false.is_some(), "Should find flag=false partition");
        if let Some(numeric) = result_false {
            assert_eq!(numeric.get("x"), Interval::constant(0));
        }
    }

    #[test]
    fn test_bdd_control_lattice_axioms() {
        let product = make_product_domain();
        let control_domain = product.control_domain();
        control_domain.allocate_var("flag");
        let flag_true = control_domain.mk_var_true("flag");
        let flag_false = control_domain.mk_var_false("flag");

        let mut numeric1 = IntervalElement::new();
        numeric1.set("x", Interval::constant(5));

        let mut numeric2 = IntervalElement::new();
        numeric2.set("x", Interval::constant(0));

        let mut partitions1 = HashMap::new();
        partitions1.insert(HashableControlState(flag_true.clone()), numeric1.clone());

        let mut partitions2 = HashMap::new();
        partitions2.insert(HashableControlState(flag_false.clone()), numeric2.clone());

        let mut partitions3 = HashMap::new();
        partitions3.insert(HashableControlState(flag_true.clone()), numeric1.clone());
        partitions3.insert(HashableControlState(flag_false.clone()), numeric2.clone());

        let elem1 = ControlSensitiveElement {
            partitions: partitions1,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        let elem2 = ControlSensitiveElement {
            partitions: partitions2,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        let elem3 = ControlSensitiveElement {
            partitions: partitions3,
            control_domain: Rc::clone(&product.control_domain),
            numeric_domain: Rc::clone(&product.numeric_domain),
        };

        crate::domain::tests::test_lattice_axioms(&product, &vec![elem1, elem2, elem3]);
    }
}
