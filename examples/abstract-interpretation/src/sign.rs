//! Sign abstract domain implementation.
//!
//! The sign domain tracks the sign of numeric values, providing a coarse
//! but very efficient abstraction. It's one of the classic examples in
//! abstract interpretation and complements finer domains like intervals.
//!
//! # Elements
//!
//! The lattice has 8 elements representing sign properties:
//! - `⊥` (Bottom): impossible/unreachable
//! - `-` (Neg): strictly negative
//! - `0` (Zero): exactly zero
//! - `+` (Pos): strictly positive
//! - `≤0` (NonPos): zero or negative
//! - `≥0` (NonNeg): zero or positive
//! - `≠0` (NonZero): negative or positive
//! - `⊤` (Top): any value
//!
//! # Lattice Structure
//!
//! ```text
//!           ⊤
//!       /   |   \
//!     ≤0   ≠0   ≥0
//!    / \  / \  / \
//!   -   0   +
//!    \  |  /
//!       ⊥
//! ```

use std::borrow::Borrow;
use std::fmt;
use std::hash::Hash;

use super::domain::AbstractDomain;
use super::expr::{NumExpr, NumPred};
use super::numeric::NumericDomain;

/// Sign values representing abstract sign properties.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    /// Bottom (`⊥`): impossible/unreachable
    Bottom,
    /// Strictly negative (`< 0`)
    Neg,
    /// Exactly zero (`= 0`)
    Zero,
    /// Strictly positive (`> 0`)
    Pos,
    /// Non-positive (`≤ 0`): `Zero ∪ Neg`
    NonPos,
    /// Non-negative (`≥ 0`): `Zero ∪ Pos`
    NonNeg,
    /// Non-zero (`≠ 0`): `Neg ∪ Pos`
    NonZero,
    /// Top (`⊤`): any value
    Top,
}

impl Sign {
    /// Check if sign contains negative values.
    pub fn has_negative(&self) -> bool {
        matches!(self, Sign::Neg | Sign::NonPos | Sign::NonZero | Sign::Top)
    }

    /// Check if sign contains zero.
    pub fn has_zero(&self) -> bool {
        matches!(self, Sign::Zero | Sign::NonPos | Sign::NonNeg | Sign::Top)
    }

    /// Check if sign contains positive values.
    pub fn has_positive(&self) -> bool {
        matches!(self, Sign::Pos | Sign::NonNeg | Sign::NonZero | Sign::Top)
    }

    /// Create sign from a concrete value.
    pub fn from_value(v: i64) -> Self {
        match v.cmp(&0) {
            std::cmp::Ordering::Less => Sign::Neg,
            std::cmp::Ordering::Equal => Sign::Zero,
            std::cmp::Ordering::Greater => Sign::Pos,
        }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sign::Bottom => write!(f, "⊥"),
            Sign::Neg => write!(f, "-"),
            Sign::Zero => write!(f, "0"),
            Sign::Pos => write!(f, "+"),
            Sign::NonPos => write!(f, "≤0"),
            Sign::NonNeg => write!(f, "≥0"),
            Sign::NonZero => write!(f, "≠0"),
            Sign::Top => write!(f, "⊤"),
        }
    }
}

/// Sign domain for abstract interpretation.
#[derive(Debug, Clone)]
pub struct SignDomain;

/// Abstract element in the sign domain (maps variables to signs).
/// Abstract element representing sign information for all variables.
///
/// Maps each program variable to a sign value representing the possible signs
/// of its values at a specific program point. This is the main data structure for
/// flow-sensitive sign analysis.
///
/// # Sign Values
///
/// Each variable can have one of:
/// - `Pos`: Always positive (> 0)
/// - `Neg`: Always negative (< 0)
/// - `Zero`: Always exactly 0
/// - `NonNeg`: Non-negative (≥20)
/// - `NonPos`: Non-positive (≤0)
/// - `NonZero`: Never zero (≠0)
/// - `Top`: Unknown/unconstrained (any sign possible)
/// - `Bottom`: Impossible (element unreachable)
///
/// # Representation
///
/// ```text
/// SignElement {
///     "x" → Pos,           // x is always positive
///     "y" → NonNeg,        // y is >= 0
///     "z" → Top,           // z's sign unknown (not in map)
/// }
/// ```
///
/// # Use Cases
///
/// - **Division-by-zero detection**: `assume(x != 0)` narrows sign to `NonZero`
/// - **Multiplication analysis**: `Pos * Neg = Neg`
/// - **Dead code detection**: Contradictory signs lead to `Bottom`
/// - **Optimization hints**: Signs can guide compiler optimizations
///
/// # Lattice Structure
///
/// The sign lattice forms a powerset-like structure:
///
/// ```text
///                     Top (⊤)  ← Unknown
///                    /  |  \
///                   /   |   \
///              Pos  Neg  Zero  NonZero
///                   \   |   /
///                 NonPos NonNeg
///                       |
///                     Bottom (⊥)  ← Unreachable
/// ```
///
/// - **Order** (⊑): More specific signs are more precise
/// - **Join** (⊔): Union of possible signs (widen to Top)
/// - **Meet** (⊓): Intersection of signs (narrow, more precise)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignElement {
    /// Mapping from variables to their sign abstractions
    pub signs: std::collections::HashMap<String, Sign>,
    /// Whether this element is bottom (unreachable)
    pub is_bottom: bool,
}

impl SignElement {
    /// Create a new empty sign element.
    pub fn new() -> Self {
        Self {
            signs: std::collections::HashMap::new(),
            is_bottom: false,
        }
    }

    /// Create a bottom element.
    pub fn bottom() -> Self {
        Self {
            signs: std::collections::HashMap::new(),
            is_bottom: true,
        }
    }

    /// Get the sign of a variable (returns Top if not defined).
    ///
    /// Returns the sign value associated with the given variable, or `Top` (unknown sign)
    /// if the variable is not explicitly constrained.
    ///
    /// # Heterogeneous Lookup
    ///
    /// Supports zero-cost lookup with `&str`:
    /// ```ignore
    /// elem.get("x");  // Works: &str accepted, no allocation
    /// ```
    pub fn get<Q>(&self, var: &Q) -> Sign
    where
        String: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        if self.is_bottom {
            return Sign::Bottom;
        }
        self.signs.get(var).copied().unwrap_or(Sign::Top)
    }

    /// Set the sign of a variable.
    pub fn set(&mut self, var: impl Into<String>, sign: Sign) {
        if sign == Sign::Bottom {
            self.is_bottom = true;
        } else {
            self.signs.insert(var.into(), sign);
        }
    }
}

impl Default for SignElement {
    fn default() -> Self {
        Self::new()
    }
}

impl AbstractDomain for SignDomain {
    type Element = SignElement;

    fn bottom(&self) -> Self::Element {
        SignElement::bottom()
    }

    fn top(&self) -> Self::Element {
        SignElement::new()
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_bottom
    }

    fn is_top(&self, _elem: &Self::Element) -> bool {
        // Element is top if all defined variables have Top sign
        // For simplicity, we don't track this precisely
        false
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        if elem1.is_bottom {
            return true;
        }
        if elem2.is_bottom {
            return false;
        }

        // elem1 ⊑ elem2 if all signs in elem1 are refined by elem2
        for (var, &s1) in &elem1.signs {
            let s2 = elem2.get(var);
            if !Self::sign_le(s1, s2) {
                return false;
            }
        }
        true
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom {
            return elem2.clone();
        }
        if elem2.is_bottom {
            return elem1.clone();
        }

        let mut result = SignElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.signs.keys().collect();
        all_vars.extend(elem2.signs.keys());

        for var in all_vars {
            let s1 = elem1.get(var);
            let s2 = elem2.get(var);
            result.set(var.clone(), Self::sign_join(s1, s2));
        }

        result
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom || elem2.is_bottom {
            return SignElement::bottom();
        }

        let mut result = SignElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.signs.keys().collect();
        all_vars.extend(elem2.signs.keys());

        for var in all_vars {
            let s1 = elem1.get(var);
            let s2 = elem2.get(var);
            let met = Self::sign_meet(s1, s2);
            if met == Sign::Bottom {
                return SignElement::bottom();
            }
            result.set(var.clone(), met);
        }

        result
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For sign domain, widening is the same as join
        // since the lattice has finite height (no infinite ascending chains)
        self.join(elem1, elem2)
    }
}

impl SignDomain {
    /// Partial order on signs: s1 ⊑ s2
    fn sign_le(s1: Sign, s2: Sign) -> bool {
        if s1 == s2 {
            return true;
        }
        match (s1, s2) {
            (Sign::Bottom, _) => true,
            (_, Sign::Top) => true,
            (Sign::Neg, Sign::NonPos | Sign::NonZero) => true,
            (Sign::Zero, Sign::NonPos | Sign::NonNeg) => true,
            (Sign::Pos, Sign::NonNeg | Sign::NonZero) => true,
            _ => false,
        }
    }

    /// Join (least upper bound) on signs.
    fn sign_join(s1: Sign, s2: Sign) -> Sign {
        if s1 == s2 {
            return s1;
        }
        match (s1, s2) {
            (Sign::Bottom, s) | (s, Sign::Bottom) => s,
            (Sign::Top, _) | (_, Sign::Top) => Sign::Top,

            // Combining opposite signs
            (Sign::Neg, Sign::Pos) | (Sign::Pos, Sign::Neg) => Sign::NonZero,
            (Sign::Neg, Sign::Zero) | (Sign::Zero, Sign::Neg) => Sign::NonPos,
            (Sign::Pos, Sign::Zero) | (Sign::Zero, Sign::Pos) => Sign::NonNeg,

            // Combining with compound signs
            (Sign::Neg, Sign::NonNeg) | (Sign::NonNeg, Sign::Neg) => Sign::Top,
            (Sign::Pos, Sign::NonPos) | (Sign::NonPos, Sign::Pos) => Sign::Top,
            (Sign::Zero, Sign::NonZero) | (Sign::NonZero, Sign::Zero) => Sign::Top,

            (Sign::Neg, Sign::NonZero) | (Sign::NonZero, Sign::Neg) => Sign::NonZero,
            (Sign::Pos, Sign::NonZero) | (Sign::NonZero, Sign::Pos) => Sign::NonZero,
            (Sign::Neg, Sign::NonPos) | (Sign::NonPos, Sign::Neg) => Sign::NonPos,
            (Sign::Zero, Sign::NonPos) | (Sign::NonPos, Sign::Zero) => Sign::NonPos,
            (Sign::Pos, Sign::NonNeg) | (Sign::NonNeg, Sign::Pos) => Sign::NonNeg,
            (Sign::Zero, Sign::NonNeg) | (Sign::NonNeg, Sign::Zero) => Sign::NonNeg,

            // Compound signs with each other
            (Sign::NonPos, Sign::NonZero) | (Sign::NonZero, Sign::NonPos) => Sign::Top,
            (Sign::NonNeg, Sign::NonZero) | (Sign::NonZero, Sign::NonNeg) => Sign::Top,
            (Sign::NonPos, Sign::NonNeg) | (Sign::NonNeg, Sign::NonPos) => Sign::Top,

            // Already handled by s1 == s2 check, but needed for exhaustiveness
            (Sign::Neg, Sign::Neg)
            | (Sign::Zero, Sign::Zero)
            | (Sign::Pos, Sign::Pos)
            | (Sign::NonPos, Sign::NonPos)
            | (Sign::NonNeg, Sign::NonNeg)
            | (Sign::NonZero, Sign::NonZero) => s1,
        }
    }

    /// Meet (greatest lower bound) on signs.
    fn sign_meet(s1: Sign, s2: Sign) -> Sign {
        if s1 == s2 {
            return s1;
        }
        match (s1, s2) {
            (Sign::Bottom, _) | (_, Sign::Bottom) => Sign::Bottom,
            (Sign::Top, s) | (s, Sign::Top) => s,

            // Intersection of disjoint signs
            (Sign::Neg, Sign::Pos) | (Sign::Pos, Sign::Neg) => Sign::Bottom,
            (Sign::Neg, Sign::Zero) | (Sign::Zero, Sign::Neg) => Sign::Bottom,
            (Sign::Pos, Sign::Zero) | (Sign::Zero, Sign::Pos) => Sign::Bottom,

            // Intersection with compound signs
            (Sign::Neg, Sign::NonPos) | (Sign::NonPos, Sign::Neg) => Sign::Neg,
            (Sign::Neg, Sign::NonZero) | (Sign::NonZero, Sign::Neg) => Sign::Neg,
            (Sign::Neg, Sign::NonNeg) | (Sign::NonNeg, Sign::Neg) => Sign::Bottom,

            (Sign::Zero, Sign::NonPos) | (Sign::NonPos, Sign::Zero) => Sign::Zero,
            (Sign::Zero, Sign::NonNeg) | (Sign::NonNeg, Sign::Zero) => Sign::Zero,
            (Sign::Zero, Sign::NonZero) | (Sign::NonZero, Sign::Zero) => Sign::Bottom,

            (Sign::Pos, Sign::NonNeg) | (Sign::NonNeg, Sign::Pos) => Sign::Pos,
            (Sign::Pos, Sign::NonZero) | (Sign::NonZero, Sign::Pos) => Sign::Pos,
            (Sign::Pos, Sign::NonPos) | (Sign::NonPos, Sign::Pos) => Sign::Bottom,

            // Compound signs with each other
            (Sign::NonPos, Sign::NonZero) | (Sign::NonZero, Sign::NonPos) => Sign::Neg,
            (Sign::NonNeg, Sign::NonZero) | (Sign::NonZero, Sign::NonNeg) => Sign::Pos,
            (Sign::NonPos, Sign::NonNeg) | (Sign::NonNeg, Sign::NonPos) => Sign::Zero,

            // Already handled by s1 == s2 check, but needed for exhaustiveness
            (Sign::Neg, Sign::Neg)
            | (Sign::Zero, Sign::Zero)
            | (Sign::Pos, Sign::Pos)
            | (Sign::NonPos, Sign::NonPos)
            | (Sign::NonNeg, Sign::NonNeg)
            | (Sign::NonZero, Sign::NonZero) => s1,
        }
    }
}

impl NumericDomain for SignDomain {
    type Var = String;
    type Value = i64;

    fn constant(&self, var: impl Into<Self::Var>, value: Self::Value) -> Self::Element {
        let mut elem = SignElement::new();
        elem.set(var.into(), Sign::from_value(value));
        elem
    }

    fn interval(&self, var: impl Into<Self::Var>, low: Self::Value, high: Self::Value) -> Self::Element {
        let mut elem = SignElement::new();
        let sign = if low > high {
            Sign::Bottom
        } else if low > 0 {
            Sign::Pos
        } else if high < 0 {
            Sign::Neg
        } else if low == 0 && high == 0 {
            Sign::Zero
        } else if low == 0 && high > 0 {
            Sign::NonNeg
        } else if low < 0 && high == 0 {
            Sign::NonPos
        } else {
            // low < 0 && high > 0
            Sign::Top
        };
        elem.set(var.into(), sign);
        elem
    }

    fn assign(&self, elem: &Self::Element, var: impl Into<Self::Var>, expr: &NumExpr<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        let value_sign = self.eval_expr(elem, expr);
        let mut result = elem.clone();
        result.set(var.into(), value_sign);
        result
    }

    fn assume(&self, elem: &Self::Element, pred: &NumPred<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        match pred {
            NumPred::Eq(NumExpr::Var(v), NumExpr::Const(n)) | NumPred::Eq(NumExpr::Const(n), NumExpr::Var(v)) => {
                let sign = Sign::from_value(*n);
                let current = elem.get(v);
                if let Some(false) = current.can_eq(sign) {
                    return self.bottom();
                }
                let mut result = elem.clone();
                result.set(v.clone(), sign);
                result
            }

            NumPred::Lt(NumExpr::Var(v), NumExpr::Const(n)) => {
                let sign = if *n <= 0 {
                    Sign::Neg
                } else if *n == 1 {
                    Sign::NonPos
                } else {
                    Sign::Top // Could be negative or zero or positive
                };
                let mut refined = SignElement::new();
                refined.set(v.clone(), sign);
                self.meet_element(elem, &refined)
            }

            NumPred::Le(NumExpr::Var(v), NumExpr::Const(n)) => {
                let sign = if *n < 0 {
                    Sign::Neg
                } else if *n == 0 {
                    Sign::NonPos
                } else {
                    Sign::Top
                };
                let mut refined = SignElement::new();
                refined.set(v.clone(), sign);
                self.meet_element(elem, &refined)
            }

            NumPred::Gt(NumExpr::Var(v), NumExpr::Const(n)) => {
                let sign = if *n >= 0 {
                    Sign::Pos
                } else if *n == -1 {
                    Sign::NonNeg
                } else {
                    Sign::Top
                };
                let mut refined = SignElement::new();
                refined.set(v.clone(), sign);
                self.meet_element(elem, &refined)
            }

            NumPred::Ge(NumExpr::Var(v), NumExpr::Const(n)) => {
                let sign = if *n > 0 {
                    Sign::Pos
                } else if *n == 0 {
                    Sign::NonNeg
                } else {
                    Sign::Top
                };
                let mut refined = SignElement::new();
                refined.set(v.clone(), sign);
                self.meet_element(elem, &refined)
            }

            NumPred::Neq(NumExpr::Var(v), NumExpr::Const(0)) | NumPred::Neq(NumExpr::Const(0), NumExpr::Var(v)) => {
                let current = elem.get(v);
                if current == Sign::Zero {
                    return self.bottom();
                }
                let mut result = elem.clone();
                if current == Sign::NonPos || current == Sign::NonNeg || current == Sign::Top {
                    result.set(
                        v.clone(),
                        if current == Sign::NonPos {
                            Sign::Neg
                        } else if current == Sign::NonNeg {
                            Sign::Pos
                        } else {
                            Sign::NonZero
                        },
                    );
                }
                result
            }

            _ => elem.clone(), // Unsupported predicates: keep element as-is
        }
    }

    fn project<Q>(&self, elem: &Self::Element, var: &Q) -> Self::Element
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        if elem.is_bottom {
            return elem.clone();
        }
        let mut result = elem.clone();
        result.signs.remove(var);
        result
    }

    fn get_constant<Q>(&self, elem: &Self::Element, var: &Q) -> Option<Self::Value>
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        if elem.is_bottom {
            return None;
        }
        let sign = elem.get(var);
        if sign == Sign::Zero {
            Some(0)
        } else {
            None
        }
    }

    fn get_bounds<Q>(&self, elem: &Self::Element, var: &Q) -> Option<(Self::Value, Self::Value)>
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        if elem.is_bottom {
            return None;
        }
        let sign = elem.get(var);
        match sign {
            Sign::Bottom => None,
            Sign::Zero => Some((0, 0)),
            Sign::Neg => Some((i64::MIN, -1)),
            Sign::Pos => Some((1, i64::MAX)),
            Sign::NonPos => Some((i64::MIN, 0)),
            Sign::NonNeg => Some((0, i64::MAX)),
            Sign::NonZero => Some((i64::MIN, i64::MAX)), // Can't represent with one interval
            Sign::Top => Some((i64::MIN, i64::MAX)),
        }
    }
}

impl SignDomain {
    /// Evaluate a numeric expression to a sign.
    fn eval_expr(&self, elem: &SignElement, expr: &NumExpr<String, i64>) -> Sign {
        match expr {
            NumExpr::Var(v) => elem.get(v),
            NumExpr::Const(n) => Sign::from_value(*n),
            NumExpr::Add(e1, e2) => {
                let s1 = self.eval_expr(elem, e1);
                let s2 = self.eval_expr(elem, e2);
                s1.add(s2)
            }
            NumExpr::Sub(e1, e2) => {
                let s1 = self.eval_expr(elem, e1);
                let s2 = self.eval_expr(elem, e2);
                s1.sub(s2)
            }
            NumExpr::Mul(e1, e2) => {
                // Special case: x * x is always non-negative
                if let (NumExpr::Var(v1), NumExpr::Var(v2)) = (e1.as_ref(), e2.as_ref()) {
                    if v1 == v2 {
                        let s = elem.get(v1);
                        // Any value squared is non-negative
                        return if s == Sign::Bottom {
                            Sign::Bottom
                        } else if s == Sign::Zero {
                            Sign::Zero
                        } else if s == Sign::Pos {
                            Sign::Pos // Positive squared is positive
                        } else if s == Sign::Neg {
                            Sign::Pos // Negative squared is positive
                        } else {
                            Sign::NonNeg // NonNeg, NonPos, NonZero, Top -> could be zero
                        };
                    }
                }
                let s1 = self.eval_expr(elem, e1);
                let s2 = self.eval_expr(elem, e2);
                s1.mul(s2)
            }
            NumExpr::Div(e1, e2) => {
                let s1 = self.eval_expr(elem, e1);
                let s2 = self.eval_expr(elem, e2);
                s1.div(s2)
            }
            NumExpr::Neg(e) => {
                let s = self.eval_expr(elem, e);
                s.neg()
            }
            NumExpr::Mod(e1, e2) => {
                let s1 = self.eval_expr(elem, e1);
                let s2 = self.eval_expr(elem, e2);
                // Modulo is complex: result has same sign as dividend (in Rust)
                if s2.has_zero() {
                    Sign::Top // Undefined if divisor can be zero
                } else {
                    s1 // Simplified: modulo preserves sign of dividend
                }
            }
        }
    }

    /// Helper to meet two elements.
    fn meet_element(&self, elem1: &SignElement, elem2: &SignElement) -> SignElement {
        self.meet(elem1, elem2)
    }
}

impl Sign {
    /// Addition on signs.
    pub fn add(self, other: Sign) -> Sign {
        use Sign::*;

        if self == Bottom || other == Bottom {
            return Bottom;
        }
        if self == Top || other == Top {
            return Top;
        }

        match (self, other) {
            // Zero is identity
            (Zero, s) | (s, Zero) => s,

            // Same sign - strictly positive/negative preserved
            (Pos, Pos) => Pos,
            (Neg, Neg) => Neg,

            // Positive combinations
            (Pos, NonNeg) | (NonNeg, Pos) | (NonNeg, NonNeg) => NonNeg,

            // Negative combinations
            (Neg, NonPos) | (NonPos, Neg) | (NonPos, NonPos) => NonPos,

            // Opposite signs - uncertain
            (Pos, Neg) | (Neg, Pos) | (Pos, NonPos) | (NonPos, Pos) | (Neg, NonNeg) | (NonNeg, Neg) => Top,

            // NonZero combinations
            (NonZero, Pos) | (Pos, NonZero) => NonZero, // Could be pos or neg, but not zero
            (NonZero, Neg) | (Neg, NonZero) => NonZero,
            (NonZero, NonZero) => Top, // Could be zero if they cancel
            (NonZero, NonPos) | (NonPos, NonZero) => Top,
            (NonZero, NonNeg) | (NonNeg, NonZero) => Top,

            _ => Top,
        }
    }

    /// Subtraction on signs.
    pub fn sub(self, other: Sign) -> Sign {
        self.add(other.neg())
    }

    /// Multiplication on signs.
    pub fn mul(self, other: Sign) -> Sign {
        use Sign::*;

        if self == Bottom || other == Bottom {
            return Bottom;
        }

        // Zero absorbs
        if self == Zero || other == Zero {
            return Zero;
        }

        if self == Top || other == Top {
            return Top;
        }

        match (self, other) {
            // Same sign → positive
            (Pos, Pos) | (Neg, Neg) => Pos,

            // Opposite sign → negative
            (Pos, Neg) | (Neg, Pos) => Neg,

            // Non-negative combinations
            (Pos, NonNeg) | (NonNeg, Pos) | (NonNeg, NonNeg) => NonNeg,
            (Neg, NonPos) | (NonPos, Neg) | (NonPos, NonPos) => NonNeg,

            // Non-positive combinations
            (Pos, NonPos) | (NonPos, Pos) => NonPos,
            (Neg, NonNeg) | (NonNeg, Neg) => NonPos,

            // NonZero combinations
            (NonZero, Pos) | (Pos, NonZero) => NonZero,
            (NonZero, Neg) | (Neg, NonZero) => NonZero,
            (NonZero, NonZero) => NonZero,
            (NonZero, NonPos) | (NonPos, NonZero) => Top,
            (NonZero, NonNeg) | (NonNeg, NonZero) => Top,

            _ => Top,
        }
    }

    /// Division on signs.
    pub fn div(self, other: Sign) -> Sign {
        use Sign::*;

        if self == Bottom || other == Bottom {
            return Bottom;
        }

        // Division by zero or possible zero → Top
        if other == Zero || other.has_zero() {
            return Top;
        }

        // Zero divided by anything (non-zero) → Zero
        if self == Zero {
            return Zero;
        }

        if self == Top || other == Top {
            return Top;
        }

        // Similar to multiplication for signs
        match (self, other) {
            // Same sign → positive
            (Pos, Pos) | (Neg, Neg) => Pos,
            (Pos, NonNeg) | (NonNeg, Pos) => NonNeg,
            (Neg, NonPos) | (NonPos, Neg) => NonNeg,

            // Opposite sign → negative
            (Pos, Neg) | (Neg, Pos) => Neg,
            (Pos, NonPos) | (NonPos, Pos) => NonPos,
            (Neg, NonNeg) | (NonNeg, Neg) => NonPos,

            // NonZero
            (NonZero, Pos) | (Pos, NonZero) => NonZero,
            (NonZero, Neg) | (Neg, NonZero) => NonZero,
            (NonZero, NonZero) => NonZero,

            _ => Top,
        }
    }

    /// Negation on signs.
    pub fn neg(self) -> Sign {
        use Sign::*;
        match self {
            Bottom => Bottom,
            Neg => Pos,
            Zero => Zero,
            Pos => Neg,
            NonPos => NonNeg,
            NonNeg => NonPos,
            NonZero => NonZero,
            Top => Top,
        }
    }

    /// Absolute value on signs.
    pub fn abs(self) -> Sign {
        use Sign::*;
        match self {
            Bottom => Bottom,
            Neg | Pos | NonZero => NonNeg,
            Zero => Zero,
            NonPos | NonNeg => NonNeg,
            Top => NonNeg,
        }
    }

    /// Equality check: can s1 = s2?
    pub fn can_eq(self, other: Sign) -> Option<bool> {
        use Sign::*;

        if self == Bottom || other == Bottom {
            return None;
        }

        // Check if intersection is non-empty
        let has_overlap = match (self, other) {
            (s1, s2) if s1 == s2 => true,
            (Top, _) | (_, Top) => true,

            // Basic signs
            (Neg, Neg) | (Zero, Zero) | (Pos, Pos) => true,
            (Neg, Zero) | (Zero, Neg) | (Neg, Pos) | (Pos, Neg) | (Zero, Pos) | (Pos, Zero) => false,

            // Compound signs
            (Neg, NonPos) | (NonPos, Neg) => true,
            (Neg, NonNeg) | (NonNeg, Neg) => false,
            (Neg, NonZero) | (NonZero, Neg) => true,

            (Zero, NonPos) | (NonPos, Zero) => true,
            (Zero, NonNeg) | (NonNeg, Zero) => true,
            (Zero, NonZero) | (NonZero, Zero) => false,

            (Pos, NonPos) | (NonPos, Pos) => false,
            (Pos, NonNeg) | (NonNeg, Pos) => true,
            (Pos, NonZero) | (NonZero, Pos) => true,

            (NonPos, NonNeg) | (NonNeg, NonPos) => true,
            (NonPos, NonZero) | (NonZero, NonPos) => true,
            (NonNeg, NonZero) | (NonZero, NonNeg) => true,

            _ => true,
        };

        if !has_overlap {
            Some(false)
        } else if self == other && !matches!(self, Top) {
            Some(true)
        } else {
            None
        }
    }

    /// Less than check: is s1 < s2 definitely true/false?
    pub fn can_lt(self, other: Sign) -> Option<bool> {
        use Sign::*;

        if self == Bottom || other == Bottom {
            return None;
        }

        match (self, other) {
            // Definitely true
            (Neg, Pos) | (Neg, NonNeg) | (NonPos, Pos) => Some(true),

            // Definitely false (same value or greater)
            (Pos, Neg) | (Pos, NonPos) | (NonNeg, Neg) => Some(false),
            (Zero, Zero) => Some(false),

            // Unknown
            _ => None,
        }
    }

    /// Less than or equal check: is s1 ≤ s2 definitely true/false?
    pub fn can_le(self, other: Sign) -> Option<bool> {
        use Sign::*;

        if self == Bottom || other == Bottom {
            return None;
        }

        match (self, other) {
            // Definitely true
            (Neg, _) if matches!(other, Neg | Zero | Pos | NonPos | NonNeg | NonZero | Top) => Some(true),
            (NonPos, Pos) | (NonPos, NonNeg) | (Neg, Pos) | (Neg, NonNeg) => Some(true),
            (Zero, Pos) | (Zero, NonNeg) => Some(true),
            (s1, s2) if s1 == s2 => Some(true),

            // Definitely false
            (Pos, Neg) | (Pos, NonPos) | (NonNeg, Neg) => Some(false),

            // Unknown
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sign_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;

        let domain = SignDomain;

        // Sample elements for testing
        let samples = vec![
            domain.bottom(),
            domain.constant("x", -5),
            domain.constant("x", 0),
            domain.constant("x", 5),
            domain.top(),
            // Non-singleton signs
            {
                let mut elem = SignElement::new();
                elem.set("x", Sign::NonPos);
                elem
            },
            {
                let mut elem = SignElement::new();
                elem.set("x", Sign::NonNeg);
                elem
            },
            {
                let mut elem = SignElement::new();
                elem.set("x", Sign::NonZero);
                elem
            },
        ];

        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_sign_properties() {
        assert!(Sign::Neg.has_negative());
        assert!(!Sign::Neg.has_zero());
        assert!(!Sign::Neg.has_positive());

        assert!(!Sign::Zero.has_negative());
        assert!(Sign::Zero.has_zero());
        assert!(!Sign::Zero.has_positive());

        assert!(!Sign::Pos.has_negative());
        assert!(!Sign::Pos.has_zero());
        assert!(Sign::Pos.has_positive());

        assert!(Sign::Top.has_negative());
        assert!(Sign::Top.has_zero());
        assert!(Sign::Top.has_positive());
    }

    #[test]
    fn test_sign_from_value() {
        assert_eq!(Sign::from_value(-5), Sign::Neg);
        assert_eq!(Sign::from_value(0), Sign::Zero);
        assert_eq!(Sign::from_value(42), Sign::Pos);
    }

    #[test]
    fn test_sign_addition() {
        use Sign::*;

        // Identity
        assert_eq!(Pos.add(Zero), Pos);
        assert_eq!(Zero.add(Neg), Neg);

        // Same sign
        assert_eq!(Pos.add(Pos), Pos);
        assert_eq!(Neg.add(Neg), Neg);

        // Opposite signs
        assert_eq!(Pos.add(Neg), Top);
        assert_eq!(Neg.add(Pos), Top);

        // Bottom propagation
        assert_eq!(Bottom.add(Pos), Bottom);
        assert_eq!(Neg.add(Bottom), Bottom);
    }

    #[test]
    fn test_sign_subtraction() {
        use Sign::*;

        assert_eq!(Pos.sub(Pos), Top); // Could be any sign
        assert_eq!(Pos.sub(Neg), Pos); // Positive - negative = positive
        assert_eq!(Neg.sub(Pos), Neg); // Negative - positive = negative
        assert_eq!(Zero.sub(Pos), Neg);
    }

    #[test]
    fn test_sign_multiplication() {
        use Sign::*;

        // Zero absorbs
        assert_eq!(Zero.mul(Pos), Zero);
        assert_eq!(Neg.mul(Zero), Zero);

        // Same signs → positive
        assert_eq!(Pos.mul(Pos), Pos);
        assert_eq!(Neg.mul(Neg), Pos);

        // Opposite signs → negative
        assert_eq!(Pos.mul(Neg), Neg);
        assert_eq!(Neg.mul(Pos), Neg);

        // NonZero
        assert_eq!(NonZero.mul(NonZero), NonZero);
    }

    #[test]
    fn test_sign_division() {
        use Sign::*;

        // Zero numerator
        assert_eq!(Zero.div(Pos), Zero);
        assert_eq!(Zero.div(Neg), Zero);

        // Division by zero or possible zero → Top
        assert_eq!(Pos.div(Zero), Top);
        assert_eq!(Pos.div(NonPos), Top); // Could be div by zero

        // Same signs → positive
        assert_eq!(Pos.div(Pos), Pos);
        assert_eq!(Neg.div(Neg), Pos);

        // Opposite signs → negative
        assert_eq!(Pos.div(Neg), Neg);
        assert_eq!(Neg.div(Pos), Neg);
    }

    #[test]
    fn test_sign_negation() {
        use Sign::*;

        assert_eq!(Neg.neg(), Pos);
        assert_eq!(Zero.neg(), Zero);
        assert_eq!(Pos.neg(), Neg);
        assert_eq!(NonPos.neg(), NonNeg);
        assert_eq!(NonNeg.neg(), NonPos);
        assert_eq!(NonZero.neg(), NonZero);
        assert_eq!(Top.neg(), Top);
    }

    #[test]
    fn test_sign_abs() {
        use Sign::*;

        assert_eq!(Neg.abs(), NonNeg);
        assert_eq!(Zero.abs(), Zero);
        assert_eq!(Pos.abs(), NonNeg);
        assert_eq!(NonZero.abs(), NonNeg);
        assert_eq!(Top.abs(), NonNeg);
    }

    #[test]
    fn test_sign_can_eq() {
        use Sign::*;

        // Definitely can be equal
        assert_eq!(Pos.can_eq(Pos), Some(true));
        assert_eq!(Zero.can_eq(Zero), Some(true));

        // Definitely cannot be equal
        assert_eq!(Pos.can_eq(Neg), Some(false));
        assert_eq!(Zero.can_eq(Pos), Some(false));
        assert_eq!(Neg.can_eq(NonNeg), Some(false));

        // Unknown
        assert_eq!(NonPos.can_eq(NonNeg), None);
        assert_eq!(Top.can_eq(Pos), None);
    }

    #[test]
    fn test_sign_can_lt() {
        use Sign::*;

        // Definitely true
        assert_eq!(Neg.can_lt(Pos), Some(true));
        assert_eq!(NonPos.can_lt(Pos), Some(true));

        // Definitely false
        assert_eq!(Pos.can_lt(Neg), Some(false));
        assert_eq!(Zero.can_lt(Zero), Some(false));

        // Unknown
        assert_eq!(NonZero.can_lt(Pos), None);
    }

    #[test]
    fn test_sign_can_le() {
        use Sign::*;

        // Definitely true
        assert_eq!(Neg.can_le(Neg), Some(true));
        assert_eq!(Neg.can_le(NonPos), Some(true));
        assert_eq!(Zero.can_le(Pos), Some(true));
        assert_eq!(NonPos.can_le(NonNeg), Some(true)); // Both contain 0

        // Definitely false
        assert_eq!(Pos.can_le(Neg), Some(false));
        assert_eq!(NonNeg.can_le(Neg), Some(false));

        // Unknown
        assert_eq!(Top.can_le(Pos), None);
    }

    #[test]
    fn test_sign_numeric_domain_constant() {
        let domain = SignDomain;

        let elem = domain.constant("x", 42);
        assert_eq!(elem.get("x"), Sign::Pos);

        let elem = domain.constant("y", 0);
        assert_eq!(elem.get("y"), Sign::Zero);

        let elem = domain.constant("z", -10);
        assert_eq!(elem.get("z"), Sign::Neg);
    }

    #[test]
    fn test_sign_numeric_domain_interval() {
        let domain = SignDomain;

        let elem = domain.interval("x", 1, 100);
        assert_eq!(elem.get("x"), Sign::Pos);

        let elem = domain.interval("x", -50, -1);
        assert_eq!(elem.get("x"), Sign::Neg);

        let elem = domain.interval("x", -10, 10);
        assert_eq!(elem.get("x"), Sign::Top);

        let elem = domain.interval("x", 0, 0);
        assert_eq!(elem.get("x"), Sign::Zero);

        let elem = domain.interval("x", 0, 50);
        assert_eq!(elem.get("x"), Sign::NonNeg);

        let elem = domain.interval("x", -50, 0);
        assert_eq!(elem.get("x"), Sign::NonPos);

        let elem = domain.interval("x", 10, 5);
        assert_eq!(elem.get("x"), Sign::Bottom);
    }

    #[test]
    fn test_sign_numeric_domain_assign() {
        use NumExpr::*;
        let domain = SignDomain;

        let mut elem = SignElement::new();
        elem.set("x", Sign::Pos);
        elem.set("y", Sign::Neg);

        // z := x + y
        let expr = Add(Box::new(Var("x".to_string())), Box::new(Var("y".to_string())));
        let result = domain.assign(&elem, "z", &expr);
        assert_eq!(result.get("z"), Sign::Top); // Pos + Neg = Top

        // z := x * y
        let expr = Mul(Box::new(Var("x".to_string())), Box::new(Var("y".to_string())));
        let result = domain.assign(&elem, "z", &expr);
        assert_eq!(result.get("z"), Sign::Neg); // Pos * Neg = Neg
    }

    #[test]
    fn test_sign_numeric_domain_assume() {
        use NumExpr::*;
        use NumPred::*;
        let domain = SignDomain;

        let mut elem = SignElement::new();
        elem.set("x", Sign::Top);

        // Assume x = 0
        let result = domain.assume(&elem, &Eq(Var("x".to_string()), Const(0)));
        assert_eq!(result.get("x"), Sign::Zero);

        // Assume x > 0
        let result = domain.assume(&elem, &Gt(Var("x".to_string()), Const(0)));
        assert_eq!(result.get("x"), Sign::Pos);

        // Assume x < 0
        let result = domain.assume(&elem, &Lt(Var("x".to_string()), Const(0)));
        assert_eq!(result.get("x"), Sign::Neg);
    }

    #[test]
    fn test_sign_get_constant() {
        let domain = SignDomain;

        let elem = domain.constant("x", 0);
        assert_eq!(domain.get_constant(&elem, "x"), Some(0));

        let elem = domain.constant("x", 42);
        assert_eq!(domain.get_constant(&elem, "x"), None);
    }

    #[test]
    fn test_sign_get_bounds() {
        let domain = SignDomain;

        let elem = domain.constant("x", 0);
        assert_eq!(domain.get_bounds(&elem, "x"), Some((0, 0)));

        let elem = domain.interval("x", 1, 100);
        assert_eq!(domain.get_bounds(&elem, "x"), Some((1, i64::MAX)));

        let elem = domain.interval("x", -50, -1);
        assert_eq!(domain.get_bounds(&elem, "x"), Some((i64::MIN, -1)));
    }

    #[test]
    fn test_sign_project() {
        let domain = SignDomain;

        let mut elem = SignElement::new();
        elem.set("x", Sign::Pos);
        elem.set("y", Sign::Neg);

        let result = domain.project(&elem, "x");
        assert_eq!(result.get("x"), Sign::Top); // x no longer constrained
        assert_eq!(result.get("y"), Sign::Neg); // y unchanged
    }

    #[test]
    fn test_sign_square_always_nonneg() {
        // Based on sign_analysis.rs Example 2
        let domain = SignDomain;

        let mut elem = SignElement::new();
        elem.set("x", Sign::Top);

        // x * x should always be non-negative
        let expr = NumExpr::var("x").mul(NumExpr::var("x"));

        let result = domain.assign(&elem, "temp", &expr);
        assert_eq!(result.get("temp"), Sign::NonNeg);

        // Test with different signs
        elem.set("y", Sign::Neg);
        let expr = NumExpr::var("y").mul(NumExpr::var("y"));
        let result = domain.assign(&elem, "temp", &expr);
        assert_eq!(result.get("temp"), Sign::Pos);

        elem.set("z", Sign::Pos);
        let expr = NumExpr::var("z").mul(NumExpr::var("z"));
        let result = domain.assign(&elem, "temp", &expr);
        assert_eq!(result.get("temp"), Sign::Pos);
    }

    #[test]
    fn test_sign_division_by_zero_detection() {
        // Based on sign_analysis.rs Example 1
        let domain = SignDomain;

        let mut elem = SignElement::new();
        elem.set("x", Sign::Top);

        // After x > 0, division is safe
        let pred = NumExpr::var("x").gt(NumExpr::constant(0));
        let elem_safe = domain.assume(&elem, &pred);
        assert_eq!(elem_safe.get("x"), Sign::Pos);
        assert!(!elem_safe.get("x").has_zero());

        // After x <= 0, division is unsafe
        let pred = NumExpr::var("x").le(NumExpr::constant(0));
        let elem_unsafe = domain.assume(&elem, &pred);
        assert!(elem_unsafe.get("x").has_zero());
    }

    #[test]
    fn test_sign_loop_invariant() {
        // Based on sign_analysis.rs Example 3
        let domain = SignDomain;

        // i = 0
        let mut elem = domain.constant("i", 0);
        assert_eq!(elem.get("i"), Sign::Zero);

        // i = i + 1 (first iteration: 0 + 1 = 1, which is Pos)
        let expr = NumExpr::var("i").add(NumExpr::constant(1));
        elem = domain.assign(&elem, "i", &expr);
        assert_eq!(elem.get("i"), Sign::Pos);

        // Join with 0 to simulate loop: Zero ⊔ Pos = NonNeg
        let elem0 = domain.constant("i", 0);
        elem = domain.join(&elem0, &elem);
        assert_eq!(elem.get("i"), Sign::NonNeg);

        // Fixed point: NonNeg + 1 = NonNeg
        let elem2 = domain.assign(&elem, "i", &expr);
        assert_eq!(elem2.get("i"), Sign::NonNeg);
        assert!(domain.le(&elem, &elem2));
    }
}
