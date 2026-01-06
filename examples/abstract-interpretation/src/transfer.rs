//! Abstract transfer functions for program statements.

use super::domain::AbstractDomain;
#[allow(unused_imports)]
use super::expr::{NumExpr, NumPred, Stmt};
use super::numeric::NumericDomain;

/// Abstract transfer function for statements.
///
/// Implements abstract semantics: `⟦stmt⟧♯ : Element -> Element`.
///
/// A transfer function is usually used together with a fixpoint engine for loops.
pub trait TransferFunction<D: AbstractDomain> {
    /// Type of program variables
    type Var: Clone;

    /// Apply the transfer function: `⟦stmt⟧♯(elem)`.
    fn apply(&self, domain: &D, elem: &D::Element, stmt: &Stmt<Self::Var>) -> D::Element;
}

/// Transfer function for numeric domains.
///
/// Handles `skip`, assignments, sequencing, conditionals (by splitting and joining),
/// `assert`/`assume` (as refinement), and `havoc` (as projection).
///
/// Note: `while` is intentionally left as a no-op placeholder; use
/// [`crate::fixpoint::FixpointEngine`] to compute loop invariants.
pub struct NumericTransferFunction;

impl<D> TransferFunction<D> for NumericTransferFunction
where
    D: NumericDomain<Value = i64>,
    D::Var: Clone,
{
    type Var = D::Var;

    fn apply(&self, domain: &D, elem: &D::Element, stmt: &Stmt<Self::Var>) -> D::Element {
        if domain.is_bottom(elem) {
            return elem.clone();
        }

        match stmt {
            Stmt::Skip => elem.clone(),

            Stmt::Assign(var, expr) => domain.assign(elem, var.clone(), expr),

            Stmt::Seq(s1, s2) => {
                let e1 = self.apply(domain, elem, s1);
                self.apply(domain, &e1, s2)
            }

            Stmt::If(pred, then_stmt, else_stmt) => {
                // Then branch
                let then_elem = domain.assume(elem, pred);
                let then_result = self.apply(domain, &then_elem, then_stmt);

                // Else branch: assume ¬pred (simplified)
                let else_pred = pred.clone().not();
                let else_elem = domain.assume(elem, &else_pred);
                let else_result = self.apply(domain, &else_elem, else_stmt);

                // Join results
                domain.join(&then_result, &else_result)
            }

            Stmt::While(_pred, _body) => {
                // For while loops, fixpoint computation should be done externally
                // This is a placeholder
                elem.clone()
            }

            Stmt::Assert(pred) => {
                // Assert refines the state
                domain.assume(elem, pred)
            }

            Stmt::Assume(pred) => domain.assume(elem, pred),

            Stmt::Havoc(var) => {
                // Non-deterministic assignment: forget variable
                domain.project(elem, var)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interval::{Bound, Interval, IntervalDomain, IntervalElement};

    #[test]
    fn test_assignment() {
        let domain = IntervalDomain;
        let transfer = NumericTransferFunction;

        let elem = {
            let mut e = IntervalElement::new();
            e.set("x", Interval::new(Bound::Finite(0), Bound::Finite(10)));
            e
        };

        // x := x + 1
        let stmt = Stmt::assign("x", NumExpr::var("x").add(NumExpr::constant(1)));

        let result = transfer.apply(&domain, &elem, &stmt);
        let x_result = result.get("x");

        assert_eq!(x_result.low, Bound::Finite(1));
        assert_eq!(x_result.high, Bound::Finite(11));
    }

    #[test]
    fn test_conditional() {
        let domain = IntervalDomain;
        let transfer = NumericTransferFunction;

        let elem = {
            let mut e = IntervalElement::new();
            e.set("x", Interval::new(Bound::Finite(-10), Bound::Finite(10)));
            e
        };

        // if (x >= 0) { x := x + 10 } else { x := -x }
        let stmt = Stmt::if_stmt(
            NumExpr::var("x").ge(NumExpr::constant(0)),
            Stmt::assign("x", NumExpr::var("x").add(NumExpr::constant(10))),
            Stmt::assign("x", NumExpr::var("x").neg()),
        );

        let result = transfer.apply(&domain, &elem, &stmt);
        let x_result = result.get("x");

        // Then: x ∈ [0, 10] + 10 = [10, 20]
        // Else: x ∈ [-10, -1], -x = [1, 10]
        // Join: [1, 20]
        assert_eq!(x_result.low, Bound::Finite(1));
        assert_eq!(x_result.high, Bound::Finite(20));
    }
}
