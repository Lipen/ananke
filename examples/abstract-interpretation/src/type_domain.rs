//! Type abstract domain.
//!
//! This module tracks possible runtime types for each value, which is useful for dynamically typed
//! languages or code with polymorphic values.
//!
//! The element domain is a finite powerset lattice over [`Type`]:
//!
//! ```text
//! Elements:  sets of types
//! ⊥:         empty set
//! ⊤:         all types ("unknown")
//! Order:     A ⊑ B  iff  A ⊆ B
//! Join:      A ⊔ B = A ∪ B
//! Meet:      A ⊓ B = A ∩ B
//! ```
//!
//! Since the carrier set is finite, widening (`∇`) is implemented as join (`⊔`).

use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::domain::AbstractDomain;

/// Represents a concrete runtime type in the analyzed language.
///
/// This enum enumerates the fundamental types that the analysis tracks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    /// Integer numbers (e.g., `42`, `-1`).
    Integer,
    /// Floating-point numbers (e.g., `3.14`, `1.0e-5`).
    Float,
    /// Boolean values (`true`, `false`).
    Boolean,
    /// String literals.
    String,
    /// Complex objects or structures.
    Object,
    /// The null or undefined value.
    Null,
    // Add more types as needed for specific languages (e.g., Array, Function).
}

/// Represents an abstract value in the type domain.
///
/// It can be:
/// - `Bottom`: No type (contradiction/unreachable).
/// - `Set`: A specific non-empty set of possible types.
/// - `Top`: Any type (unknown).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeSet {
    /// Represents the empty set of types.
    Bottom,
    /// Represents a specific subset of types.
    /// Invariant: The set is never empty. An empty set is represented by `Bottom`.
    Set(BTreeSet<Type>),
    /// Represents the set of all possible types.
    Top,
}

/// The Type Abstract Domain.
///
/// This struct implements the [`AbstractDomain`] trait with [`TypeSet`] as elements.
#[derive(Clone, Debug)]
pub struct TypeDomain;

impl TypeDomain {
    /// Creates a new `TypeDomain`.
    pub fn new() -> Self {
        TypeDomain
    }

    /// Creates an abstract value representing a single concrete type.
    pub fn from_type(&self, t: Type) -> TypeSet {
        let mut set = BTreeSet::new();
        set.insert(t);
        TypeSet::Set(set)
    }

    /// Creates an abstract value representing a set of concrete types.
    pub fn from_types(&self, types: &[Type]) -> TypeSet {
        if types.is_empty() {
            return TypeSet::Bottom;
        }
        let mut set = BTreeSet::new();
        for &t in types {
            set.insert(t);
        }
        TypeSet::Set(set)
    }

    /// Checks if the abstract value represents *exactly* the given type (and no other).
    ///
    /// Returns `true` if the set contains only `t`.
    pub fn is_exactly(&self, elem: &TypeSet, t: Type) -> bool {
        match elem {
            TypeSet::Set(s) => s.len() == 1 && s.contains(&t),
            _ => false,
        }
    }

    /// Checks if the abstract value *may* contain the given type.
    ///
    /// Returns `true` if `t` is in the set of possible types, or if the value is `Top`.
    pub fn may_be(&self, elem: &TypeSet, t: Type) -> bool {
        match elem {
            TypeSet::Bottom => false,
            TypeSet::Top => true,
            TypeSet::Set(s) => s.contains(&t),
        }
    }

    /// Checks if the abstract value represents a numeric type (Integer or Float).
    pub fn is_numeric(&self, elem: &TypeSet) -> bool {
        match elem {
            TypeSet::Bottom => false,
            TypeSet::Top => true, // Could be numeric
            TypeSet::Set(s) => s.iter().any(|t| matches!(t, Type::Integer | Type::Float)),
        }
    }
}

impl Default for TypeDomain {
    fn default() -> Self {
        Self::new()
    }
}

impl AbstractDomain for TypeDomain {
    type Element = TypeSet;

    /// Returns the bottom element (`⊥`), representing the empty set of types.
    fn bottom(&self) -> Self::Element {
        TypeSet::Bottom
    }

    /// Returns the top element (`⊤`), representing the set of all types.
    fn top(&self) -> Self::Element {
        TypeSet::Top
    }

    /// Checks if the element is bottom.
    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, TypeSet::Bottom)
    }

    /// Checks if the element is top.
    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, TypeSet::Top)
    }

    /// Partial order check: `elem1 ⊑ elem2`.
    ///
    /// Returns true if the set of types in `elem1` is a subset of `elem2`.
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (TypeSet::Bottom, _) => true,
            (_, TypeSet::Top) => true,
            (TypeSet::Top, _) => false,    // Top <= X only if X is Top (handled above)
            (_, TypeSet::Bottom) => false, // X <= Bottom only if X is Bottom (handled above)
            (TypeSet::Set(s1), TypeSet::Set(s2)) => s1.is_subset(s2),
        }
    }

    /// Join operation (`⊔`): Set union.
    ///
    /// Returns a new element containing all types present in either `elem1` or `elem2`.
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (TypeSet::Bottom, e) | (e, TypeSet::Bottom) => e.clone(),
            (TypeSet::Top, _) | (_, TypeSet::Top) => TypeSet::Top,
            (TypeSet::Set(s1), TypeSet::Set(s2)) => {
                let mut res = s1.clone();
                res.extend(s2.iter().cloned());
                TypeSet::Set(res)
            }
        }
    }

    /// Meet operation (`⊓`): Set intersection.
    ///
    /// Returns a new element containing only types present in both `elem1` and `elem2`.
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (TypeSet::Bottom, _) | (_, TypeSet::Bottom) => TypeSet::Bottom,
            (TypeSet::Top, e) | (e, TypeSet::Top) => e.clone(),
            (TypeSet::Set(s1), TypeSet::Set(s2)) => {
                let res: BTreeSet<Type> = s1.intersection(s2).cloned().collect();
                if res.is_empty() {
                    TypeSet::Bottom
                } else {
                    TypeSet::Set(res)
                }
            }
        }
    }

    /// Widening operator (`∇`).
    ///
    /// Since the type lattice is finite, widening is identical to join.
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lattice_order() {
        let d = TypeDomain::new();
        let bot = d.bottom();
        let top = d.top();
        let t_int = d.from_type(Type::Integer);
        let t_str = d.from_type(Type::String);
        let t_int_str = d.join(&t_int, &t_str);

        // Reflexivity
        assert!(d.le(&bot, &bot));
        assert!(d.le(&top, &top));
        assert!(d.le(&t_int, &t_int));

        // Bottom is least element
        assert!(d.le(&bot, &t_int));
        assert!(d.le(&bot, &top));

        // Top is greatest element
        assert!(d.le(&t_int, &top));
        assert!(d.le(&t_int_str, &top));

        // Subset relationships
        assert!(d.le(&t_int, &t_int_str));
        assert!(d.le(&t_str, &t_int_str));
        assert!(!d.le(&t_int_str, &t_int));
        assert!(!d.le(&t_int, &t_str));
    }

    #[test]
    fn test_join() {
        let d = TypeDomain::new();
        let t_int = d.from_type(Type::Integer);
        let t_float = d.from_type(Type::Float);
        let t_bool = d.from_type(Type::Boolean);

        let j1 = d.join(&t_int, &t_float);
        assert!(d.may_be(&j1, Type::Integer));
        assert!(d.may_be(&j1, Type::Float));
        assert!(!d.may_be(&j1, Type::Boolean));

        let j2 = d.join(&j1, &t_bool);
        assert!(d.may_be(&j2, Type::Integer));
        assert!(d.may_be(&j2, Type::Float));
        assert!(d.may_be(&j2, Type::Boolean));

        // Join with bottom is identity
        assert_eq!(d.join(&t_int, &d.bottom()), t_int);

        // Join with top is top
        assert!(d.is_top(&d.join(&t_int, &d.top())));
    }

    #[test]
    fn test_meet() {
        let d = TypeDomain::new();
        let t_int = d.from_type(Type::Integer);
        let t_float = d.from_type(Type::Float);
        let t_num = d.join(&t_int, &t_float);

        // Intersection of disjoint sets is bottom
        assert!(d.is_bottom(&d.meet(&t_int, &t_float)));

        // Intersection with subset
        assert_eq!(d.meet(&t_num, &t_int), t_int);

        // Meet with top is identity
        assert_eq!(d.meet(&t_int, &d.top()), t_int);

        // Meet with bottom is bottom
        assert!(d.is_bottom(&d.meet(&t_int, &d.bottom())));
    }

    #[test]
    fn test_helper_methods() {
        let d = TypeDomain::new();
        let t_int = d.from_type(Type::Integer);
        let t_float = d.from_type(Type::Float);
        let t_str = d.from_type(Type::String);
        let t_num = d.join(&t_int, &t_float);

        assert!(d.is_exactly(&t_int, Type::Integer));
        assert!(!d.is_exactly(&t_num, Type::Integer));
        assert!(!d.is_exactly(&d.top(), Type::Integer));

        assert!(d.may_be(&t_int, Type::Integer));
        assert!(d.may_be(&t_num, Type::Integer));
        assert!(d.may_be(&d.top(), Type::Integer));
        assert!(!d.may_be(&t_str, Type::Integer));

        assert!(d.is_numeric(&t_int));
        assert!(d.is_numeric(&t_float));
        assert!(d.is_numeric(&t_num));
        assert!(!d.is_numeric(&t_str));
        assert!(d.is_numeric(&d.top())); // Top may be numeric
        assert!(!d.is_numeric(&d.bottom()));
    }

    #[test]
    fn test_from_types() {
        let d = TypeDomain::new();
        let empty = d.from_types(&[]);
        assert!(d.is_bottom(&empty));

        let single = d.from_types(&[Type::Integer]);
        assert!(d.is_exactly(&single, Type::Integer));

        let multi = d.from_types(&[Type::Integer, Type::String]);
        assert!(d.may_be(&multi, Type::Integer));
        assert!(d.may_be(&multi, Type::String));
        assert!(!d.may_be(&multi, Type::Boolean));
    }

    #[test]
    fn test_type_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;
        let domain = TypeDomain::new();
        let samples = vec![
            domain.bottom(),
            domain.top(),
            domain.from_type(Type::Integer),
            domain.from_type(Type::Float),
            domain.from_types(&[Type::Integer, Type::Float]),
        ];
        test_lattice_axioms(&domain, &samples);
    }
}
