//! Core abstract domain trait and utilities.

use std::fmt::Debug;

/// Abstract domain interface.
///
/// A domain provides a lattice of abstract elements together with the usual operations.
/// The intended reading is “`a ⊑ b` means `a` is at least as precise as `b`”.
///
/// ```text
/// Reflexive:      a ⊑ a
/// Transitive:     a ⊑ b ∧ b ⊑ c  =>  a ⊑ c
/// Antisymmetric:  a ⊑ b ∧ b ⊑ a  =>  a = b
/// ```
pub trait AbstractDomain: Clone + Debug + Sized {
    /// The type representing abstract elements.
    type Element: Clone + Debug;

    /// Bottom element (`⊥`), representing the empty set of concrete states.
    fn bottom(&self) -> Self::Element;

    /// Top element (`⊤`), representing “any state is possible”.
    fn top(&self) -> Self::Element;

    /// Check if an element is bottom.
    fn is_bottom(&self, elem: &Self::Element) -> bool;

    /// Check if an element is top.
    fn is_top(&self, elem: &Self::Element) -> bool;

    /// Partial order (`⊑`).
    ///
    /// Returns `true` iff `elem1` is at least as precise as `elem2`.
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool;

    /// Join (`⊔`): least upper bound (merge / over-approximation).
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Meet (`⊓`): greatest lower bound (refinement).
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Widening (`∇`) used during fixpoint iteration.
    ///
    /// Must satisfy `elem1 ⊑ (elem1 ∇ elem2)` and should enforce convergence on
    /// infinite-height domains.
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element;

    /// Narrowing (`△`) after widening.
    ///
    /// The default uses meet (`⊓`), which is safe and typically applied for a small
    /// bounded number of iterations.
    fn narrow(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.meet(elem1, elem2)
    }

    /// Check equality of abstract elements.
    fn eq(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        self.le(elem1, elem2) && self.le(elem2, elem1)
    }

    /// Join multiple elements.
    fn join_many<I>(&self, elems: I) -> Self::Element
    where
        I: IntoIterator<Item = Self::Element>,
    {
        elems.into_iter().fold(self.bottom(), |acc, e| self.join(&acc, &e))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    /// Test helper: validate basic lattice axioms
    pub fn test_lattice_axioms<D: AbstractDomain>(domain: &D, samples: &[D::Element]) {
        for a in samples {
            // Reflexivity: a ⊑ a
            assert!(domain.le(a, a), "Reflexivity failed for {:?}", a);

            // Identity: a ⊔ ⊥ = a
            let a_join_bot = domain.join(a, &domain.bottom());
            assert!(domain.eq(a, &a_join_bot), "Join with bottom failed for {:?}", a);

            // Identity: a ⊓ ⊥ = ⊥
            let a_join_top = domain.join(a, &domain.top());
            assert!(domain.eq(&a_join_top, &domain.top()), "Join with top failed for {:?}", a);

            // Identity: a ⊓ ⊤ = a
            let a_meet_top = domain.meet(a, &domain.top());
            assert!(domain.eq(a, &a_meet_top), "Meet with top failed for {:?}", a);

            // Identity: a ⊓ ⊥ = ⊥
            let a_meet_bot = domain.meet(a, &domain.bottom());
            assert!(domain.eq(&a_meet_bot, &domain.bottom()), "Meet with bottom failed for {:?}", a);

            // Widening preserves order: a ⊑ (a ∇ b)
            for b in samples {
                let widened = domain.widen(a, b);
                assert!(domain.le(a, &widened), "Widening does not preserve order for {:?} and {:?}", a, b);
            }
        }

        for a in samples {
            for b in samples {
                // Commutativity: a ⊔ b = b ⊔ a
                let a_join_b = domain.join(a, b);
                let b_join_a = domain.join(b, a);
                assert!(domain.eq(&a_join_b, &b_join_a), "Join commutativity failed for {:?} and {:?}", a, b);

                // Commutativity: a ⊓ b = b ⊓ a
                let a_meet_b = domain.meet(a, b);
                let b_meet_a = domain.meet(b, a);
                assert!(domain.eq(&a_meet_b, &b_meet_a), "Meet commutativity failed for {:?} and {:?}", a, b);

                // Join upper bound: a ⊑ (a ⊔ b)
                assert!(domain.le(a, &a_join_b), "Join is not upper bound for a: {:?} and {:?}", a, b);
                assert!(domain.le(b, &a_join_b), "Join is not upper bound for b: {:?} and {:?}", a, b);

                // Meet lower bound: (a ⊓ b) ⊑ a
                assert!(domain.le(&a_meet_b, a), "Meet is not lower bound of a: {:?} and {:?}", a, b);
                assert!(domain.le(&a_meet_b, b), "Meet is not lower bound of b: {:?} and {:?}", a, b);
            }
        }
    }
}
