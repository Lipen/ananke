//! Interaction functions and their representation.
//!
//! An interaction function I: {0,1}ᵏ → {0,1} captures how k child
//! subfunctions combine to produce the parent function's output.

use std::fmt;

use bit_vec::BitVec;

pub use crate::separability::Operator;

/// An interaction function on k inputs.
///
/// Represented as a truth table with 2ᵏ entries.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct InteractionFunction {
    /// Number of inputs (arity).
    arity: u32,
    /// Truth table: 2^arity bits.
    table: BitVec,
}

impl InteractionFunction {
    /// Create an interaction function from an expression.
    pub fn from_expr(arity: u32, f: impl Fn(&[bool]) -> bool) -> Self {
        let size = 1usize << arity;
        let mut table = BitVec::with_capacity(size);
        let mut input = vec![false; arity as usize];

        for i in 0..size {
            for (j, val) in input.iter_mut().enumerate() {
                *val = (i >> j) & 1 == 1;
            }
            table.push(f(&input));
        }

        InteractionFunction { arity, table }
    }

    /// Create from a raw truth table.
    pub fn from_table(arity: u32, table: BitVec) -> Self {
        assert_eq!(table.len(), 1 << arity);
        InteractionFunction { arity, table }
    }

    /// Create the identity function (projection on first input).
    pub fn identity() -> Self {
        InteractionFunction::from_expr(1, |x| x[0])
    }

    /// Create a binary operator as an interaction function.
    pub fn from_binary(op: Operator) -> Self {
        InteractionFunction::from_expr(2, |xs| op.apply(xs[0], xs[1]))
    }

    /// Create a k-ary interaction function from a given operator.
    pub fn from_op(op: Operator, arity: u32) -> Self {
        InteractionFunction::from_expr(arity, |xs| op.apply_all(xs))
    }

    /// Create the AND interaction function on k inputs.
    pub fn and_all(arity: u32) -> Self {
        Self::from_op(Operator::And, arity)
    }

    /// Create the OR interaction function on k inputs.
    pub fn or_all(arity: u32) -> Self {
        Self::from_op(Operator::Or, arity)
    }

    /// Create the XOR interaction function on k inputs.
    pub fn xor_all(arity: u32) -> Self {
        Self::from_op(Operator::Xor, arity)
    }

    /// Get the arity (number of inputs).
    pub fn arity(&self) -> u32 {
        self.arity
    }

    /// Get the table size (2^arity).
    pub fn size(&self) -> usize {
        self.table.len()
    }

    /// Evaluate the interaction function.
    pub fn eval(&self, inputs: &[bool]) -> bool {
        assert_eq!(inputs.len(), self.arity as usize);
        let index = inputs.iter().enumerate().fold(0usize, |acc, (i, &b)| acc | ((b as usize) << i));
        self.table[index]
    }

    /// Check if this is the constant 0 function.
    pub fn is_zero(&self) -> bool {
        !self.table.any()
    }

    /// Check if this is the constant 1 function.
    pub fn is_one(&self) -> bool {
        self.table.all()
    }

    /// Check if this is a projection (identity on one input).
    pub fn is_projection(&self) -> Option<usize> {
        for i in 0..self.arity as usize {
            let is_proj_i = (0..self.size()).all(|idx| {
                let expected = (idx >> i) & 1 == 1;
                self.table[idx] == expected
            });
            if is_proj_i {
                return Some(i);
            }
        }
        None
    }

    /// Check if this is a binary operator.
    pub fn as_binary_operator(&self) -> Option<Operator> {
        if self.arity != 2 {
            return None;
        }

        for op in Operator::all() {
            let op_func = InteractionFunction::from_binary(op);
            if self.table == op_func.table {
                return Some(op);
            }
        }
        None
    }

    /// Check if this interaction function matches a symmetric operator (AND/OR/XOR) of any arity.
    ///
    /// Returns the operator if the function is exactly AND-all, OR-all, or XOR-all.
    pub fn as_symmetric_operator(&self) -> Option<Operator> {
        if self.arity < 2 {
            return None;
        }
        // Check against n-ary versions of AND, OR, XOR
        let arity = self.arity;
        for op in Operator::all() {
            let op_func = InteractionFunction::from_op(op, arity);
            if self.table == op_func.table {
                return Some(op);
            }
        }
        None
    }

    /// Reorder inputs according to a permutation.
    ///
    /// `perm[i]` gives the new position of input i.
    pub fn reorder(&self, perm: &[usize]) -> Self {
        assert_eq!(perm.len(), self.arity as usize);

        InteractionFunction::from_expr(self.arity, |new_x| {
            // Map new inputs to old
            let mut old_x = vec![false; self.arity as usize];
            for (old_i, &new_i) in perm.iter().enumerate() {
                old_x[old_i] = new_x[new_i];
            }
            self.eval(&old_x)
        })
    }

    /// Get the raw truth table.
    pub fn table(&self) -> &BitVec {
        &self.table
    }
}

impl fmt::Debug for InteractionFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "I{}[{}]", self.arity, self.table)
    }
}

impl fmt::Display for InteractionFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Try to display as a known operator
        if self.arity == 2 {
            if let Some(op) = self.as_binary_operator() {
                return write!(f, "{}", op);
            }
        }

        // For arity 1, check for identity or negation
        if self.arity == 1 {
            if self.is_projection().is_some() {
                return write!(f, "id");
            }
            if self.table[0] && !self.table[1] {
                return write!(f, "¬");
            }
        }

        // Fall back to truth table representation
        write!(f, "I{}[{}]", self.arity, self.table)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_operators() {
        let and_f = InteractionFunction::from_binary(Operator::And);
        assert_eq!(and_f.eval(&[false, false]), false);
        assert_eq!(and_f.eval(&[true, false]), false);
        assert_eq!(and_f.eval(&[false, true]), false);
        assert_eq!(and_f.eval(&[true, true]), true);

        let or_f = InteractionFunction::from_binary(Operator::Or);
        assert_eq!(or_f.eval(&[false, false]), false);
        assert_eq!(or_f.eval(&[true, true]), true);

        let xor_f = InteractionFunction::from_binary(Operator::Xor);
        assert_eq!(xor_f.eval(&[false, false]), false);
        assert_eq!(xor_f.eval(&[true, false]), true);
        assert_eq!(xor_f.eval(&[true, true]), false);
    }

    #[test]
    fn test_recognition() {
        let and_f = InteractionFunction::from_binary(Operator::And);
        assert_eq!(and_f.as_binary_operator(), Some(Operator::And));

        let identity = InteractionFunction::identity();
        assert_eq!(identity.is_projection(), Some(0));
    }

    #[test]
    fn test_multiway() {
        let and3 = InteractionFunction::and_all(3);
        assert!(!and3.eval(&[true, true, false]));
        assert!(and3.eval(&[true, true, true]));

        let xor3 = InteractionFunction::xor_all(3);
        assert!(xor3.eval(&[true, false, false]));
        assert!(xor3.eval(&[true, true, true]));
        assert!(!xor3.eval(&[true, true, false]));
    }

    #[test]
    fn test_reorder() {
        // f(x, y) = x ∧ y
        let f = InteractionFunction::from_binary(Operator::And);

        // Swap inputs: f'(x, y) = f(y, x) = y ∧ x = x ∧ y
        let f_swapped = f.reorder(&[1, 0]);

        // AND is commutative, so they should be equal
        assert_eq!(f.table, f_swapped.table);

        // Now test with a non-commutative function: f(x, y) = x ∧ ¬y
        let g = InteractionFunction::from_expr(2, |x| x[0] && !x[1]);
        let g_swapped = g.reorder(&[1, 0]); // g'(x, y) = y ∧ ¬x

        // These should be different
        assert_ne!(g.table, g_swapped.table);
    }
}
