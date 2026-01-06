//! SDD-backed control domain.
//!
//! Elements are SDD formulas representing feasible control states.
//! The lattice operations follow boolean semantics:
//! - order: `φ ⊑ ψ` iff `φ => ψ`,
//! - join: `φ ⊔ ψ = φ ∨ ψ`,
//! - meet: `φ ⊓ ψ = φ ∧ ψ`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use ananke_sdd::{SddId, SddManager};
use num_bigint::BigUint;

use crate::AbstractDomain;

/// Control state encoded as an SDD.
#[derive(Clone)]
pub struct SddControlState {
    phi: SddId,
    manager: Rc<SddManager>,
}

impl SddControlState {
    /// Wrap a raw SDD node as a control-state element.
    pub fn new(phi: SddId, manager: Rc<SddManager>) -> Self {
        Self { phi, manager }
    }

    /// Return the underlying SDD node.
    pub fn phi(&self) -> SddId {
        self.phi
    }
}

impl PartialEq for SddControlState {
    fn eq(&self, other: &Self) -> bool {
        self.phi == other.phi
    }
}

impl Eq for SddControlState {}

impl fmt::Debug for SddControlState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.manager.is_false(self.phi) {
            write!(f, "SddControlState(⊥)")
        } else if self.manager.is_true(self.phi) {
            write!(f, "SddControlState(⊤)")
        } else {
            write!(f, "SddControlState({})", self.phi)
        }
    }
}

/// Path-sensitive control domain backed by SDDs.
#[derive(Clone)]
pub struct SddControlDomain {
    manager: Rc<SddManager>,
    var_map: Rc<RefCell<HashMap<String, u32>>>,
    capacity: u32,
}

impl SddControlDomain {
    /// Create a new domain with a fixed number of variables.
    pub fn new(num_vars: u32) -> Self {
        Self {
            manager: Rc::new(SddManager::new(num_vars)),
            var_map: Rc::new(RefCell::new(HashMap::new())),
            capacity: num_vars,
        }
    }

    /// Get shared manager.
    pub fn manager(&self) -> &Rc<SddManager> {
        &self.manager
    }

    /// Allocate or retrieve a variable ID (1-indexed).
    pub fn allocate_var(&self, name: &str) -> u32 {
        if let Some(id) = self.var_map.borrow().get(name).copied() {
            return id;
        }

        let next = self.var_map.borrow().len() as u32 + 1;
        assert!(next <= self.capacity, "exceeded declared SDD variable capacity");
        self.var_map.borrow_mut().insert(name.to_string(), next);
        next
    }

    /// Construct a state that enforces `name` to be true.
    pub fn mk_var_true(&self, name: &str) -> SddControlState {
        let var_id = self.allocate_var(name);
        let phi = self.manager.var(var_id);
        SddControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Construct a state that enforces `name` to be false.
    pub fn mk_var_false(&self, name: &str) -> SddControlState {
        let var_id = self.allocate_var(name);
        let phi = self.manager.neg_var(var_id);
        SddControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Conjunction (`a ∧ b`).
    pub fn and(&self, a: &SddControlState, b: &SddControlState) -> SddControlState {
        let phi = self.manager.and(a.phi, b.phi);
        SddControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Disjunction (`a ∨ b`).
    pub fn or(&self, a: &SddControlState, b: &SddControlState) -> SddControlState {
        let phi = self.manager.or(a.phi, b.phi);
        SddControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Negation (`¬a`).
    pub fn not(&self, a: &SddControlState) -> SddControlState {
        let phi = self.manager.negate(a.phi);
        SddControlState::new(phi, Rc::clone(&self.manager))
    }

    /// Check implication (`a => b`).
    pub fn implies(&self, a: &SddControlState, b: &SddControlState) -> bool {
        let impl_sdd = self.manager.implies(a.phi, b.phi);
        self.manager.is_true(impl_sdd)
    }

    /// Count satisfying assignments for this control state.
    pub fn model_count(&self, state: &SddControlState) -> BigUint {
        self.manager.model_count(state.phi)
    }
}

impl Default for SddControlDomain {
    fn default() -> Self {
        Self::new(1)
    }
}

impl fmt::Debug for SddControlDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SddControlDomain")
            .field("num_vars", &self.capacity)
            .field("allocated", &self.var_map.borrow().keys().collect::<Vec<_>>())
            .finish()
    }
}

impl AbstractDomain for SddControlDomain {
    type Element = SddControlState;

    fn bottom(&self) -> Self::Element {
        SddControlState::new(self.manager.false_sdd(), Rc::clone(&self.manager))
    }

    fn top(&self) -> Self::Element {
        SddControlState::new(self.manager.true_sdd(), Rc::clone(&self.manager))
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        self.manager.is_false(elem.phi)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        self.manager.is_true(elem.phi)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        let impl_sdd = self.manager.implies(elem1.phi, elem2.phi);
        self.manager.is_true(impl_sdd)
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.or(elem1, elem2)
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.and(elem1, elem2)
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lattice_axioms_hold() {
        let domain = SddControlDomain::new(3);
        let a = domain.mk_var_true("a");
        let b = domain.mk_var_false("a");
        let c = domain.mk_var_true("b");

        let samples = vec![domain.top(), domain.bottom(), a.clone(), b.clone(), c.clone(), domain.and(&a, &c)];
        crate::domain::tests::test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn implication_works() {
        let domain = SddControlDomain::new(2);
        let x = domain.mk_var_true("x");
        let not_x = domain.mk_var_false("x");
        assert!(domain.implies(&x, &domain.join(&x, &not_x)));
        assert!(!domain.implies(&x, &not_x));
    }
}
