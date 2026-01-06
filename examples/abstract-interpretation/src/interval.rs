//! Interval abstract domain.
//!
//! `Interval` represents sets of integers of the form `[low, high]` with
//! `low`/`high` possibly infinite.
//! The lattice order is reverse-inclusion on bounds:
//! ` [l1, h1] ⊑ [l2, h2]  <=>  l2 <= l1  and  h1 <= h2 `.
//!
//! `IntervalElement` lifts intervals to a flow-sensitive environment:
//! a partial map `Var -> Interval` where absence means `⊤`.

use std::borrow::Borrow;
use std::cmp::{max, min};
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

use super::domain::AbstractDomain;
use super::expr::{NumExpr, NumPred};
use super::numeric::NumericDomain;

/// A bound in an interval lattice.
///
/// Represents an endpoint: negative infinity, a finite i64 value, or positive infinity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bound {
    NegInf,
    Finite(i64),
    PosInf,
}

impl Bound {
    /// Extract the finite value, if any.
    pub fn as_finite(&self) -> Option<i64> {
        match self {
            Bound::Finite(n) => Some(*n),
            _ => None,
        }
    }

    /// Add two bounds with saturation and infinity rules.
    pub fn add(&self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_add(*b)),
            (Bound::NegInf, Bound::PosInf) | (Bound::PosInf, Bound::NegInf) => {
                // Undefined: use top
                Bound::PosInf
            }
            (Bound::NegInf, _) | (_, Bound::NegInf) => Bound::NegInf,
            (Bound::PosInf, _) | (_, Bound::PosInf) => Bound::PosInf,
        }
    }

    /// Subtract two bounds with saturation and infinity rules.
    pub fn sub(&self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_sub(*b)),
            (Bound::PosInf, Bound::NegInf) => Bound::PosInf,
            (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
            (Bound::PosInf, _) => Bound::PosInf,
            (Bound::NegInf, _) => Bound::NegInf,
            (_, Bound::PosInf) => Bound::NegInf,
            (_, Bound::NegInf) => Bound::PosInf,
        }
    }

    /// Multiply two bounds with saturation and infinity rules.
    pub fn mul(&self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a.saturating_mul(*b)),
            (Bound::Finite(0), _) | (_, Bound::Finite(0)) => Bound::Finite(0),
            (Bound::NegInf, Bound::PosInf) | (Bound::PosInf, Bound::NegInf) => Bound::NegInf,
            (Bound::NegInf, Bound::NegInf) | (Bound::PosInf, Bound::PosInf) => Bound::PosInf,
            _ => Bound::PosInf, // Simplified
        }
    }

    /// Negate a bound: `-∞ ↔ +∞`, finite values negated, top stays top.
    pub fn neg(&self) -> Bound {
        match self {
            Bound::NegInf => Bound::PosInf,
            Bound::Finite(n) => Bound::Finite(-n),
            Bound::PosInf => Bound::NegInf,
        }
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bound::NegInf => write!(f, "-∞"),
            Bound::Finite(n) => write!(f, "{}", n),
            Bound::PosInf => write!(f, "+∞"),
        }
    }
}

/// A numeric interval `[low, high]` representing a set of possible values.
///
/// Forms a lattice with join (union), meet (intersection), and widening operations.
/// The empty interval `[+∞, -∞]` represents unreachable states.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval {
    pub low: Bound,
    pub high: Bound,
}

impl Interval {
    /// The empty interval (bottom element).
    pub const EMPTY: Self = Self {
        low: Bound::PosInf,
        high: Bound::NegInf,
    };

    /// Create an interval, or the empty interval if `low > high`.
    pub fn new(low: Bound, high: Bound) -> Self {
        if low > high {
            Self::EMPTY
        } else {
            Self { low, high }
        }
    }

    /// An interval containing exactly one value.
    pub fn constant(value: i64) -> Self {
        Self {
            low: Bound::Finite(value),
            high: Bound::Finite(value),
        }
    }

    /// Top element: unconstrained bounds `[-∞, +∞]`.
    pub fn top() -> Self {
        Self {
            low: Bound::NegInf,
            high: Bound::PosInf,
        }
    }

    /// Bottom element: empty interval (unreachable state).
    pub fn bottom() -> Self {
        Self {
            low: Bound::PosInf,
            high: Bound::NegInf,
        }
    }

    /// Check if this interval is empty.
    pub fn is_empty(&self) -> bool {
        self.low > self.high
    }

    /// Test membership: whether `value` is in this interval.
    pub fn contains(&self, value: i64) -> bool {
        match (self.low, self.high) {
            (Bound::Finite(l), Bound::Finite(h)) => l <= value && value <= h,
            (Bound::NegInf, Bound::Finite(h)) => value <= h,
            (Bound::Finite(l), Bound::PosInf) => l <= value,
            (Bound::NegInf, Bound::PosInf) => true,
            _ => false,
        }
    }

    /// Join: smallest interval containing both (union).
    pub fn join(&self, other: &Interval) -> Interval {
        if self.is_empty() {
            return *other;
        }
        if other.is_empty() {
            return *self;
        }
        Interval {
            low: min(self.low, other.low),
            high: max(self.high, other.high),
        }
    }

    /// Meet: intersection of the two intervals.
    pub fn meet(&self, other: &Interval) -> Interval {
        Interval::new(max(self.low, other.low), min(self.high, other.high))
    }

    /// Widen: extrapolate bounds to infinity to accelerate convergence.
    pub fn widen(&self, other: &Interval) -> Interval {
        let low = if other.low < self.low { Bound::NegInf } else { self.low };
        let high = if other.high > self.high { Bound::PosInf } else { self.high };
        Interval { low, high }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.low, self.high)
    }
}

/// Interval abstract domain: tracks numeric bounds per variable.
///
/// Implements flow-sensitive interval analysis over program states (`IntervalElement`).
/// Provides abstract transfer functions for assignments and predicates.
///
/// **Limitations**: Cannot express relational constraints (e.g., `x < y`) and
/// imprecise with disjunctive properties. Use constraint propagation for refinement.
#[derive(Debug, Clone)]
pub struct IntervalDomain;

/// Abstract program state mapping variables to their interval bounds.
///
/// Example: `{"i" → [0, 10], "sum" → [0, 45]}` represents a program point where
/// `i` ranges from 0-10 and `sum` from 0-45.
///
/// **Special states:**
/// - Bottom (`is_bottom = true`): Unreachable code (contradictory constraints)
/// - Top (variable not in map): Unconstrained (any value possible)
/// - Empty interval (`[+∞, -∞]`): Impossible constraint → triggers bottom
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalElement {
    pub intervals: HashMap<String, Interval>,
    pub is_bottom: bool,
}

impl IntervalElement {
    /// Create an empty environment (all variables unconstrained).
    pub fn new() -> Self {
        Self {
            intervals: HashMap::new(),
            is_bottom: false,
        }
    }

    /// Bottom element (unreachable state).
    pub fn bottom() -> Self {
        Self {
            intervals: HashMap::new(),
            is_bottom: true,
        }
    }

    /// Top element (all variables unconstrained).
    pub fn top() -> Self {
        Self::new()
    }

    /// Get the interval for a variable.
    ///
    /// Returns the stored interval, or `⊤ = [-∞, +∞]` if the variable is unconstrained.
    pub fn get<Q>(&self, var: &Q) -> Interval
    where
        String: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        if self.is_bottom {
            return Interval::bottom();
        }
        self.intervals.get(var).copied().unwrap_or(Interval::top())
    }

    /// Set the interval for a variable.
    ///
    /// If the interval is empty, marks the element as bottom (unreachable).
    pub fn set(&mut self, var: impl Into<String>, interval: Interval) {
        if interval.is_empty() {
            self.is_bottom = true;
        } else {
            self.intervals.insert(var.into(), interval);
        }
    }
}

impl Default for IntervalElement {
    fn default() -> Self {
        Self::new()
    }
}

impl AbstractDomain for IntervalDomain {
    type Element = IntervalElement;

    /// Bottom element: unreachable program state (contradictory interval constraints).
    fn bottom(&self) -> Self::Element {
        IntervalElement::bottom()
    }

    /// Top element: all variables unconstrained.
    fn top(&self) -> Self::Element {
        IntervalElement::top()
    }

    /// Check if intervals represent unreachable state (empty or contradictory).
    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_bottom
    }

    fn is_top(&self, _elem: &Self::Element) -> bool {
        // Element is top if all variables have infinite intervals
        // For simplicity, we don't track this precisely
        false
    }

    /// Order: `e1 ⊑ e2` iff for every variable `x`, `e1(x) ⊑ e2(x)`.
    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        if elem1.is_bottom {
            return true;
        }
        if elem2.is_bottom {
            return false;
        }

        // elem1 ⊑ elem2 if all intervals in elem1 are contained in elem2
        for (var, i1) in &elem1.intervals {
            let i2 = elem2.get(var);
            if i1.low < i2.low || i1.high > i2.high {
                return false;
            }
        }
        true
    }

    /// Join: component-wise interval join.
    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom {
            return elem2.clone();
        }
        if elem2.is_bottom {
            return elem1.clone();
        }

        let mut result = IntervalElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.intervals.keys().collect();
        all_vars.extend(elem2.intervals.keys());

        for var in all_vars {
            let i1 = elem1.get(var);
            let i2 = elem2.get(var);
            result.set(var.clone(), i1.join(&i2));
        }

        result
    }

    /// Meet: component-wise interval meet; returns `⊥` on contradiction.
    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom || elem2.is_bottom {
            return IntervalElement::bottom();
        }

        let mut result = IntervalElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.intervals.keys().collect();
        all_vars.extend(elem2.intervals.keys());

        for var in all_vars {
            let i1 = elem1.get(var);
            let i2 = elem2.get(var);
            let met = i1.meet(&i2);
            if met.is_empty() {
                return IntervalElement::bottom();
            }
            result.set(var.clone(), met);
        }

        result
    }

    /// Widen: extrapolates per-variable intervals to `±∞` when bounds grow,
    /// ensuring convergence in fixpoint iteration.
    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        if elem1.is_bottom {
            return elem2.clone();
        }
        if elem2.is_bottom {
            return elem1.clone();
        }

        let mut result = IntervalElement::new();
        let mut all_vars: std::collections::HashSet<_> = elem1.intervals.keys().collect();
        all_vars.extend(elem2.intervals.keys());

        for var in all_vars {
            let i1 = elem1.get(var);
            let i2 = elem2.get(var);
            result.set(var.clone(), i1.widen(&i2));
        }

        result
    }
}

impl NumericDomain for IntervalDomain {
    type Var = String;
    type Value = i64;

    /// Create element with constant: variable gets singleton interval `[value, value]`.
    fn constant(&self, var: impl Into<Self::Var>, value: Self::Value) -> Self::Element {
        let mut elem = IntervalElement::new();
        elem.set(var.into(), Interval::constant(value));
        elem
    }

    /// Create element with interval constraint: variable gets `[low, high]`.
    fn interval(&self, var: impl Into<Self::Var>, low: Self::Value, high: Self::Value) -> Self::Element {
        let mut elem = IntervalElement::new();
        elem.set(var.into(), Interval::new(Bound::Finite(low), Bound::Finite(high)));
        elem
    }

    /// Assign `var := expr` using interval arithmetic.
    fn assign(&self, elem: &Self::Element, var: impl Into<Self::Var>, expr: &NumExpr<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        let mut result = elem.clone();
        let interval = self.eval_expr(elem, expr);
        result.set(var.into(), interval);
        result
    }

    /// Refine under a predicate using lightweight constraint propagation.
    ///
    /// Supports boolean connectives and comparisons; disjunction is approximated with `join`.
    fn assume(&self, elem: &Self::Element, pred: &NumPred<Self::Var, Self::Value>) -> Self::Element {
        if elem.is_bottom {
            return elem.clone();
        }

        // Refine abstract state based on predicate
        // Handles: all comparison patterns (var op expr, expr op var, expr op expr)
        // Supports: logical connectives (∧, ∨, ¬), equality, inequality
        match pred {
            NumPred::True => elem.clone(),
            NumPred::False => IntervalElement::bottom(),

            // Logical connectives
            NumPred::And(p1, p2) => {
                let e1 = self.assume(elem, p1);
                self.assume(&e1, p2)
            }
            NumPred::Or(p1, p2) => {
                let e1 = self.assume(elem, p1);
                let e2 = self.assume(elem, p2);
                self.join(&e1, &e2)
            }
            NumPred::Not(p) => {
                // Negate the inner predicate
                match p.as_ref() {
                    NumPred::True => IntervalElement::bottom(),
                    NumPred::False => elem.clone(),
                    NumPred::Lt(e1, e2) => self.assume(elem, &e1.clone().ge(e2.clone())),
                    NumPred::Le(e1, e2) => self.assume(elem, &e1.clone().gt(e2.clone())),
                    NumPred::Gt(e1, e2) => self.assume(elem, &e1.clone().le(e2.clone())),
                    NumPred::Ge(e1, e2) => self.assume(elem, &e1.clone().lt(e2.clone())),
                    NumPred::Eq(e1, e2) => self.assume(elem, &e1.clone().neq(e2.clone())),
                    NumPred::Neq(e1, e2) => self.assume(elem, &e1.clone().eq(e2.clone())),
                    NumPred::Not(inner) => self.assume(elem, inner),
                    NumPred::And(p1, p2) => {
                        // ¬(p1 ∧ p2) = ¬p1 ∨ ¬p2 (De Morgan)
                        self.assume(elem, &p1.clone().not().or(p2.clone().not()))
                    }
                    NumPred::Or(p1, p2) => {
                        // ¬(p1 ∨ p2) = ¬p1 ∧ ¬p2 (De Morgan)
                        self.assume(elem, &p1.clone().not().and(p2.clone().not()))
                    }
                }
            }

            // x != c (imprecise: can't represent non-contiguous intervals)
            NumPred::Neq(NumExpr::Var(v), NumExpr::Const(c)) => {
                let current = elem.get(v);
                if let (Bound::Finite(l), Bound::Finite(h)) = (current.low, current.high) {
                    if l == h && l == *c {
                        // x is exactly c, so x != c is impossible
                        return IntervalElement::bottom();
                    }
                }
                // Otherwise, we can't refine precisely (would need disjunctive domain)
                elem.clone()
            }
            NumPred::Neq(NumExpr::Const(c), NumExpr::Var(v)) => self.assume(elem, &NumExpr::var(v.clone()).neq(NumExpr::constant(*c))),
            // General Neq case: can't refine intervals for general inequality
            // (would require disjunctive domain to represent x ∈ [a,b] \ {c})
            NumPred::Neq(_, _) => elem.clone(),

            // Comparison predicates: use complex refinement for all cases
            NumPred::Lt(e1, e2) => self.refine_complex_predicate(elem, e1, e2, ComparisonOp::Lt),
            NumPred::Le(e1, e2) => self.refine_complex_predicate(elem, e1, e2, ComparisonOp::Le),
            NumPred::Gt(e1, e2) => self.refine_complex_predicate(elem, e1, e2, ComparisonOp::Gt),
            NumPred::Ge(e1, e2) => self.refine_complex_predicate(elem, e1, e2, ComparisonOp::Ge),
            NumPred::Eq(e1, e2) => self.refine_complex_predicate(elem, e1, e2, ComparisonOp::Eq),

            // Note: the default case is not needed since we exhaustively match all NumPred variants
            #[allow(unreachable_patterns)]
            _ => elem.clone(),
        }
    }

    /// Project out (remove) a variable's interval constraint from the element.
    fn project<Q>(&self, elem: &Self::Element, var: &Q) -> Self::Element
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        let mut result = elem.clone();
        result.intervals.remove(var);
        result
    }

    /// Extract exact constant if variable's interval is singleton `[c, c]`.
    fn get_constant<Q>(&self, elem: &Self::Element, var: &Q) -> Option<Self::Value>
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        let interval = elem.get(var);
        match (interval.low, interval.high) {
            (Bound::Finite(l), Bound::Finite(h)) if l == h => Some(l),
            _ => None,
        }
    }

    /// Get finite interval bounds `[low, high]` for a variable; returns `None` if bounds are infinite.
    fn get_bounds<Q>(&self, elem: &Self::Element, var: &Q) -> Option<(Self::Value, Self::Value)>
    where
        Self::Var: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        let interval = elem.get(var);
        match (interval.low, interval.high) {
            (Bound::Finite(l), Bound::Finite(h)) => Some((l, h)),
            _ => None,
        }
    }
}

impl IntervalDomain {
    /// Evaluate an expression in the current state.
    fn eval_expr(&self, elem: &IntervalElement, expr: &NumExpr<String, i64>) -> Interval {
        match expr {
            NumExpr::Const(c) => Interval::constant(*c),
            NumExpr::Var(v) => elem.get(v),
            NumExpr::Add(e1, e2) => {
                let i1 = self.eval_expr(elem, e1);
                let i2 = self.eval_expr(elem, e2);
                Interval::new(i1.low.add(&i2.low), i1.high.add(&i2.high))
            }
            NumExpr::Sub(e1, e2) => {
                let i1 = self.eval_expr(elem, e1);
                let i2 = self.eval_expr(elem, e2);
                Interval::new(i1.low.sub(&i2.high), i1.high.sub(&i2.low))
            }
            NumExpr::Mul(e1, e2) => {
                let i1 = self.eval_expr(elem, e1);
                let i2 = self.eval_expr(elem, e2);
                // Simplified: compute all four corners
                let corners = [
                    i1.low.mul(&i2.low),
                    i1.low.mul(&i2.high),
                    i1.high.mul(&i2.low),
                    i1.high.mul(&i2.high),
                ];
                let low = corners.iter().min().copied().unwrap_or(Bound::NegInf);
                let high = corners.iter().max().copied().unwrap_or(Bound::PosInf);
                Interval::new(low, high)
            }
            NumExpr::Neg(e) => {
                let i = self.eval_expr(elem, e);
                Interval::new(i.high.neg(), i.low.neg())
            }
            _ => Interval::top(), // Div, Mod: simplified
        }
    }

    /// Collect all variables in an expression.
    fn extract_vars(&self, expr: &NumExpr<String, i64>, vars: &mut std::collections::HashSet<String>) {
        match expr {
            NumExpr::Var(v) => {
                vars.insert(v.clone());
            }
            NumExpr::Const(_) => {}
            NumExpr::Add(e1, e2) | NumExpr::Sub(e1, e2) | NumExpr::Mul(e1, e2) | NumExpr::Div(e1, e2) | NumExpr::Mod(e1, e2) => {
                self.extract_vars(e1, vars);
                self.extract_vars(e2, vars);
            }
            NumExpr::Neg(e) => {
                self.extract_vars(e, vars);
            }
        }
    }

    /// Refine variables in a comparison using iterative constraint propagation.
    ///
    /// Isolates each variable and narrows its bounds until fixpoint.
    fn refine_complex_predicate(
        &self,
        elem: &IntervalElement,
        e1: &NumExpr<String, i64>,
        e2: &NumExpr<String, i64>,
        op: ComparisonOp,
    ) -> IntervalElement {
        use std::collections::HashSet;

        // Extract all variables from both expressions
        let mut vars = HashSet::new();
        self.extract_vars(e1, &mut vars);
        self.extract_vars(e2, &mut vars);

        // If no variables or already at bottom, return unchanged
        if vars.is_empty() || elem.is_bottom {
            return elem.clone();
        }

        // Iterative refinement: try to deduce bounds for each variable
        let mut current = elem.clone();
        let max_iterations = 3; // Limit iterations to avoid infinite loops

        for _ in 0..max_iterations {
            let mut changed = false;

            for var in &vars {
                // Try to isolate this variable and refine its bounds
                let old_interval = current.get(var);
                let new_interval = self.refine_variable_in_predicate(&current, var, e1, e2, op);

                if new_interval != old_interval {
                    current.set(var.clone(), new_interval);
                    changed = true;
                }
            }

            if !changed || current.is_bottom {
                break;
            }
        }

        current
    }

    /// Refine a specific variable by isolating it in a comparison.
    fn refine_variable_in_predicate(
        &self,
        elem: &IntervalElement,
        var: &str,
        e1: &NumExpr<String, i64>,
        e2: &NumExpr<String, i64>,
        op: ComparisonOp,
    ) -> Interval {
        let current = elem.get(var);

        // Try to express the constraint as: var op' bound
        // For e1 op e2, if e1 contains var, evaluate e2 and try to derive bound
        // If e2 contains var, evaluate e1 and try to derive bound

        let e1_has_var = self.contains_var(e1, var);
        let e2_has_var = self.contains_var(e2, var);

        // Special case: x + c op y + d can be rewritten as x op y + (d - c)
        if let NumExpr::Add(e1_left, e1_right) = e1 {
            if let (NumExpr::Var(v1), NumExpr::Const(c1)) = (e1_left.as_ref(), e1_right.as_ref()) {
                if let NumExpr::Add(e2_left, e2_right) = e2 {
                    if let (NumExpr::Var(v2), NumExpr::Const(c2)) = (e2_left.as_ref(), e2_right.as_ref()) {
                        if v1 == var && v2 != var {
                            // x + c1 op y + c2  =>  x op y + (c2 - c1)
                            let y_interval = elem.get(v2);
                            let adjusted = Interval::new(
                                y_interval.low.add(&Bound::Finite(c2 - c1)),
                                y_interval.high.add(&Bound::Finite(c2 - c1)),
                            );
                            return current.meet(&self.apply_comparison_bound(adjusted, op));
                        } else if v2 == var && v1 != var {
                            // y + c1 op x + c2  =>  x op' y + (c1 - c2)
                            let y_interval = elem.get(v1);
                            let adjusted = Interval::new(
                                y_interval.low.add(&Bound::Finite(c1 - c2)),
                                y_interval.high.add(&Bound::Finite(c1 - c2)),
                            );
                            return current.meet(&self.apply_comparison_bound(adjusted, op.flip()));
                        }
                    }
                }
            }
        }

        // Handle: (x + c) op e where e doesn't contain x
        if let NumExpr::Add(e1_left, e1_right) = e1 {
            if let (NumExpr::Var(v1), NumExpr::Const(c)) = (e1_left.as_ref(), e1_right.as_ref()) {
                if v1 == var && !self.contains_var(e2, var) {
                    // x + c op e2  =>  x op e2 - c
                    let i2 = self.eval_expr(elem, e2);
                    let adjusted = Interval::new(i2.low.sub(&Bound::Finite(*c)), i2.high.sub(&Bound::Finite(*c)));
                    return current.meet(&self.apply_comparison_bound(adjusted, op));
                }
            }
        }

        // Handle: e op (x + c) where e doesn't contain x
        if let NumExpr::Add(e2_left, e2_right) = e2 {
            if let (NumExpr::Var(v2), NumExpr::Const(c)) = (e2_left.as_ref(), e2_right.as_ref()) {
                if v2 == var && !self.contains_var(e1, var) {
                    // e1 op x + c  =>  x op' e1 - c
                    let i1 = self.eval_expr(elem, e1);
                    let adjusted = Interval::new(i1.low.sub(&Bound::Finite(*c)), i1.high.sub(&Bound::Finite(*c)));
                    return current.meet(&self.apply_comparison_bound(adjusted, op.flip()));
                }
            }
        }

        // General case: if only one side has the variable, refine based on the other side
        if e1_has_var && !e2_has_var {
            let i2 = self.eval_expr(elem, e2);
            return current.meet(&self.apply_comparison_bound(i2, op));
        } else if e2_has_var && !e1_has_var {
            let i1 = self.eval_expr(elem, e1);
            return current.meet(&self.apply_comparison_bound(i1, op.flip()));
        }

        // Both sides have variables or more complex patterns: return current (no refinement)
        current
    }

    /// Check if an expression contains a specific variable.
    fn contains_var(&self, expr: &NumExpr<String, i64>, var: &str) -> bool {
        match expr {
            NumExpr::Var(v) => v == var,
            NumExpr::Const(_) => false,
            NumExpr::Add(e1, e2) | NumExpr::Sub(e1, e2) | NumExpr::Mul(e1, e2) | NumExpr::Div(e1, e2) | NumExpr::Mod(e1, e2) => {
                self.contains_var(e1, var) || self.contains_var(e2, var)
            }
            NumExpr::Neg(e) => self.contains_var(e, var),
        }
    }

    /// Convert a comparison operator to an interval constraint.
    ///
    /// E.g., `x < 5` becomes `[-∞, 4]`, `x >= 10` becomes `[10, +∞]`.
    fn apply_comparison_bound(&self, bound_interval: Interval, op: ComparisonOp) -> Interval {
        match op {
            ComparisonOp::Lt => Interval::new(Bound::NegInf, bound_interval.high.sub(&Bound::Finite(1))),
            ComparisonOp::Le => Interval::new(Bound::NegInf, bound_interval.high),
            ComparisonOp::Gt => Interval::new(bound_interval.low.add(&Bound::Finite(1)), Bound::PosInf),
            ComparisonOp::Ge => Interval::new(bound_interval.low, Bound::PosInf),
            ComparisonOp::Eq => bound_interval,
        }
    }
}

/// Single-value interval domain: analyze scalar intervals directly.
///
/// Unlike [`IntervalDomain`] which tracks bounds for multiple variables,
/// this operates on individual [`Interval`] values. Use for simplified or
/// single-property analyses.
#[derive(Debug, Clone)]
pub struct SingleIntervalDomain;

impl AbstractDomain for SingleIntervalDomain {
    type Element = Interval;

    /// Bottom element (empty interval).
    fn bottom(&self) -> Self::Element {
        Interval::bottom()
    }

    fn top(&self) -> Self::Element {
        Interval::top()
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_empty()
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        *elem == Interval::top()
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        if elem1.is_empty() {
            return true;
        }
        if elem2.is_empty() {
            return false;
        }
        // elem1 <= elem2 if elem1 is contained in elem2
        // i.e. elem2.low <= elem1.low AND elem1.high <= elem2.high
        elem1.low >= elem2.low && elem1.high <= elem2.high
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        elem1.join(elem2)
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        elem1.meet(elem2)
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        elem1.widen(elem2)
    }
}

/// Comparison operator used in constraint refinement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ComparisonOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

impl ComparisonOp {
    /// Flip the comparison: `(a < b) ↔ (b > a)`.
    fn flip(self) -> Self {
        match self {
            ComparisonOp::Lt => ComparisonOp::Gt,
            ComparisonOp::Le => ComparisonOp::Ge,
            ComparisonOp::Gt => ComparisonOp::Lt,
            ComparisonOp::Ge => ComparisonOp::Le,
            ComparisonOp::Eq => ComparisonOp::Eq,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interval_operations() {
        // Intervals: [0, 10] and [5, 15]
        let i1 = Interval::new(Bound::Finite(0), Bound::Finite(10));
        let i2 = Interval::new(Bound::Finite(5), Bound::Finite(15));

        // Join: [0, 10] ⊔ [5, 15] = [0, 15]
        let joined = i1.join(&i2);
        assert_eq!(joined, Interval::new(Bound::Finite(0), Bound::Finite(15)));

        // Meet: [0, 10] ⊓ [5, 15] = [5, 10]
        let met = i1.meet(&i2);
        assert_eq!(met, Interval::new(Bound::Finite(5), Bound::Finite(10)));

        // Widening: [0, 10] ▽ [5, 15] = [0, +∞]
        let widened = i1.widen(&i2);
        assert_eq!(widened, Interval::new(Bound::Finite(0), Bound::PosInf));
    }

    #[test]
    fn test_interval_domain() {
        let domain = IntervalDomain;

        // Element: x ∈ [5, 5]
        let e1 = domain.constant("x", 5);
        assert_eq!(e1.get("x"), Interval::constant(5));

        // Element: x ∈ [0, 10]
        let e2 = domain.interval("x", 0, 10);
        assert_eq!(e2.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));

        // Join: x ∈ [0, 10]
        let joined = domain.join(&e1, &e2);
        assert_eq!(joined.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));
    }

    #[test]
    fn test_interval_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;

        let domain = IntervalDomain;

        // Create sample elements for testing
        let samples = vec![
            domain.bottom(),
            domain.top(),
            domain.constant("x", 0),
            domain.constant("x", 5),
            domain.interval("x", 0, 10),
            domain.interval("x", -5, 5),
            domain.interval("x", 10, 20),
        ];

        // Validate all lattice axioms
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_assume_reversed_comparisons() {
        let domain = IntervalDomain;

        // Test c < x (constant on left)
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::new(Bound::Finite(-10), Bound::Finite(10)));

        let pred = NumExpr::constant(0).lt(NumExpr::var("x"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(1), Bound::Finite(10)));

        // Test c <= x
        let pred = NumExpr::constant(5).le(NumExpr::var("x"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(5), Bound::Finite(10)));

        // Test c > x
        let pred = NumExpr::constant(5).gt(NumExpr::var("x"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(-10), Bound::Finite(4)));

        // Test c >= x
        let pred = NumExpr::constant(0).ge(NumExpr::var("x"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(-10), Bound::Finite(0)));
    }

    #[test]
    fn test_assume_with_expressions() {
        let domain = IntervalDomain;

        // Setup: x ∈ [0, 10], y ∈ [0, 5]
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));
        elem.set("y", Interval::new(Bound::Finite(0), Bound::Finite(5)));

        // Test x < y + 3 (x should be refined to [0, 7] since y+3 ∈ [3, 8])
        let pred = NumExpr::var("x").lt(NumExpr::var("y").add(NumExpr::constant(3)));
        let result = domain.assume(&elem, &pred);
        // x < (y+3).high = x < 8, so x ∈ [0, 7]
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(7)));

        // Test x + 2 > y (refines x to [−1, 10], but intersected with [0,10] gives [0,10])
        let pred = NumExpr::var("x").add(NumExpr::constant(2)).gt(NumExpr::var("y"));
        let result = domain.assume(&elem, &pred);
        // x+2 > y means x > y-2, y.low-2 = -2, so x ∈ [-1, 10] ∩ [0, 10] = [0, 10]
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));
    }

    #[test]
    fn test_assume_equality() {
        let domain = IntervalDomain;

        // Test x == c
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));

        let pred = NumExpr::var("x").eq(NumExpr::constant(5));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::constant(5));

        // Test c == x (reversed)
        let pred = NumExpr::constant(7).eq(NumExpr::var("x"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::constant(7));

        // Test x == y+3 where y ∈ [2, 4]
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));
        elem.set("y", Interval::new(Bound::Finite(2), Bound::Finite(4)));

        let pred = NumExpr::var("x").eq(NumExpr::var("y").add(NumExpr::constant(3)));
        let result = domain.assume(&elem, &pred);
        // x == y+3, y ∈ [2,4], so y+3 ∈ [5,7], x gets refined to [5,7]
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(5), Bound::Finite(7)));
    }

    #[test]
    fn test_assume_inequality() {
        let domain = IntervalDomain;

        // Test x != c where x is exactly c (should be bottom)
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::constant(5));

        let pred = NumExpr::var("x").neq(NumExpr::constant(5));
        let result = domain.assume(&elem, &pred);
        assert!(result.is_bottom);

        // Test x != c where x is an interval (no refinement possible)
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));

        let pred = NumExpr::var("x").neq(NumExpr::constant(5));
        let result = domain.assume(&elem, &pred);
        // Can't refine interval domain for inequality (would need disjunctive domain)
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));

        // Test c != x (reversed)
        let pred = NumExpr::constant(5).neq(NumExpr::var("x"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));
    }

    #[test]
    fn test_assume_complex_logical() {
        let domain = IntervalDomain;

        // Test (x >= 0) ∧ (x <= 5)
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::new(Bound::Finite(-10), Bound::Finite(10)));

        let pred = NumExpr::var("x")
            .ge(NumExpr::constant(0))
            .and(NumExpr::var("x").le(NumExpr::constant(5)));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(5)));

        // Test (x < 0) ∨ (x > 10)
        let pred = NumExpr::var("x")
            .lt(NumExpr::constant(0))
            .or(NumExpr::var("x").gt(NumExpr::constant(10)));
        let result = domain.assume(&elem, &pred);
        // Join of [-10, -1] and [11, 10] (empty) = [-10, -1]
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(-10), Bound::Finite(-1)));

        // Test ¬(x >= 5) which is x < 5
        let pred = NumExpr::var("x").ge(NumExpr::constant(5)).not();
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(-10), Bound::Finite(4)));
    }

    #[test]
    fn test_assume_with_expression_on_both_sides() {
        let domain = IntervalDomain;

        // Setup: x ∈ [0, 10], y ∈ [5, 15]
        let mut elem = IntervalElement::new();
        elem.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));
        elem.set("y", Interval::new(Bound::Finite(5), Bound::Finite(15)));

        // Test x + 5 <= y
        // With complex predicate refinement: x + 5 <= y means x <= y - 5
        // y.high = 15, so x <= 10, which doesn't further refine x ∈ [0, 10]
        let pred = NumExpr::var("x").add(NumExpr::constant(5)).le(NumExpr::var("y"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));

        // Test x + 5 <= y + 2, which simplifies to x <= y - 3
        // y ∈ [5, 15], so y - 3 ∈ [2, 12], thus x ∈ [0, 10] ∩ [-∞, 12] = [0, 10]
        let pred = NumExpr::var("x")
            .add(NumExpr::constant(5))
            .le(NumExpr::var("y").add(NumExpr::constant(2)));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));

        // Test with tighter constraint: x + 10 <= y
        // x + 10 <= y means x <= y - 10, y ∈ [5, 15], so x <= 5
        let pred = NumExpr::var("x").add(NumExpr::constant(10)).le(NumExpr::var("y"));
        let result = domain.assume(&elem, &pred);
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(5)));

        // Test x + y <= 20 (both variables in same expression)
        // With iterative refinement, this should refine both bounds
        let pred = NumExpr::var("x").add(NumExpr::var("y")).le(NumExpr::constant(20));
        let result = domain.assume(&elem, &pred);
        // x + y <= 20, x ∈ [0, 10], y ∈ [5, 15]
        // x <= 20 - y, y.low = 5, so x <= 15 (no refinement to x)
        // y <= 20 - x, x.low = 0, so y <= 20 (no refinement to y)
        // This case doesn't refine much without more sophisticated analysis
        assert_eq!(result.get("x"), Interval::new(Bound::Finite(0), Bound::Finite(10)));
        assert_eq!(result.get("y"), Interval::new(Bound::Finite(5), Bound::Finite(15)));
    }
}
