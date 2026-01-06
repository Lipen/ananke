//! Numeric abstract domain trait and utilities.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use super::domain::AbstractDomain;
use super::expr::{NumExpr, NumPred};

/// Numeric abstract domain for integer/real variables.
///
/// This trait extends `AbstractDomain` with operations specific to
/// numeric program analysis.
pub trait NumericDomain: AbstractDomain {
    /// Variable identifier type.
    type Var: Clone + Eq + Hash + Debug;

    /// Numeric value type.
    type Value: Clone + Debug + PartialOrd;

    /// Create element representing a constant assignment: `var = value`.
    fn constant(&self, var: impl Into<Self::Var>, value: Self::Value) -> Self::Element;

    /// Create element representing an interval constraint: `var ∈ [low, high]`.
    fn interval(&self, var: impl Into<Self::Var>, low: Self::Value, high: Self::Value) -> Self::Element;

    /// Apply assignment: `var := expr`.
    ///
    /// Returns a new abstract element where `var` is bound to the result of `expr`.
    fn assign(&self, elem: &Self::Element, var: impl Into<Self::Var>, expr: &NumExpr<Self::Var, Self::Value>) -> Self::Element;

    /// Assume a predicate holds: `elem ∧ pred`.
    ///
    /// Refines the abstract element by adding constraint `pred`.
    fn assume(&self, elem: &Self::Element, pred: &NumPred<Self::Var, Self::Value>) -> Self::Element;

    /// Project out a variable (existential quantification): `∃var. elem`.
    ///
    /// Removes all constraints on `var`.
    fn project<Q>(&self, elem: &Self::Element, var: &Q) -> Self::Element
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq;

    /// Get the constant value of a variable if it's uniquely determined.
    fn get_constant<Q>(&self, elem: &Self::Element, var: &Q) -> Option<Self::Value>
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq;

    /// Get the interval bounds for a variable: `[low, high]`.
    fn get_bounds<Q>(&self, elem: &Self::Element, var: &Q) -> Option<(Self::Value, Self::Value)>
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq;

    /// Rename variables using a substitution map.
    fn rename(&self, elem: &Self::Element, _subst: &HashMap<Self::Var, Self::Var>) -> Self::Element {
        // Default implementation: identity (can be overridden for efficiency)
        elem.clone()
    }

    /// Check if element is infeasible (bottom).
    fn is_infeasible(&self, elem: &Self::Element) -> bool {
        self.is_bottom(elem)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::NumExpr;
    use crate::interval::{Bound, Interval, IntervalDomain, IntervalElement};

    #[test]
    fn test_numeric_domain_constant() {
        let domain = IntervalDomain;
        let elem = domain.constant("x", 42);

        assert_eq!(elem.get("x"), Interval::constant(42));
        assert_eq!(domain.get_constant(&elem, "x"), Some(42));
    }

    #[test]
    fn test_numeric_domain_interval() {
        let domain = IntervalDomain;
        let elem = domain.interval("x", -10, 10);

        assert_eq!(elem.get("x"), Interval::new(Bound::Finite(-10), Bound::Finite(10)));
        assert_eq!(domain.get_bounds(&elem, "x"), Some((-10, 10)));
    }

    #[test]
    fn test_numeric_domain_assign() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(5));

        // y := x + 10
        let expr = NumExpr::var("x").add(NumExpr::constant(10));
        let result = domain.assign(&elem, "y", &expr);

        assert_eq!(result.get("x"), Interval::constant(5));
        assert_eq!(result.get("y"), Interval::constant(15));
    }

    #[test]
    fn test_numeric_domain_assign_complex() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(0), Bound::Finite(10)));
        elem.set("y".to_string(), Interval::new(Bound::Finite(5), Bound::Finite(15)));

        // z := x + y
        let expr = NumExpr::var("x").add(NumExpr::var("y"));
        let result = domain.assign(&elem, "z", &expr);

        assert_eq!(result.get("z"), Interval::new(Bound::Finite(5), Bound::Finite(25)));
    }

    #[test]
    fn test_numeric_domain_assume() {
        let domain = IntervalDomain;
        let elem = domain.interval("x", -10, 10);

        // assume(x >= 0)
        let pred = NumExpr::var("x").ge(NumExpr::constant(0));
        let refined = domain.assume(&elem, &pred);

        assert_eq!(refined.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));
    }

    #[test]
    fn test_numeric_domain_assume_contradiction() {
        let domain = IntervalDomain;
        let elem = domain.interval("x", 0, 10);

        // assume(x < 0) - contradiction
        let pred = NumExpr::var("x").lt(NumExpr::constant(0));
        let refined = domain.assume(&elem, &pred);

        assert!(domain.is_infeasible(&refined));
    }

    #[test]
    fn test_numeric_domain_project() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::constant(5));
        elem.set("y".to_string(), Interval::constant(10));

        let projected = domain.project(&elem, "x");

        // x should be removed, y should remain
        assert_eq!(projected.get("x"), Interval::top());
        assert_eq!(projected.get("y"), Interval::constant(10));
    }

    #[test]
    fn test_numeric_domain_multiple_constraints() {
        let domain = IntervalDomain;
        let elem = domain.interval("x", -100, 100);

        // assume(x >= 0)
        let pred1 = NumExpr::var("x").ge(NumExpr::constant(0));
        let refined1 = domain.assume(&elem, &pred1);

        // assume(x <= 50)
        let pred2 = NumExpr::var("x").le(NumExpr::constant(50));
        let refined2 = domain.assume(&refined1, &pred2);

        assert_eq!(refined2.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(50)));
        assert_eq!(domain.get_bounds(&refined2, "x"), Some((0, 50)));
    }

    #[test]
    fn test_numeric_domain_arithmetic_precision() {
        let domain = IntervalDomain;
        let mut elem = IntervalElement::new();
        elem.set("x".to_string(), Interval::new(Bound::Finite(1), Bound::Finite(2)));

        // y := x * x (should be [1, 4])
        let expr = NumExpr::var("x").mul(NumExpr::var("x"));
        let result = domain.assign(&elem, "y", &expr);

        assert_eq!(result.get("y"), Interval::new(Bound::Finite(1), Bound::Finite(4)));
    }
}
