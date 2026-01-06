//! Fixpoint computation engine with widening and narrowing.

use super::domain::AbstractDomain;

/// Fixpoint computation engine.
///
/// Computes least/greatest fixpoints of monotone functions over
/// abstract domains, using widening to ensure termination.
#[derive(Debug, Clone)]
pub struct FixpointEngine<D: AbstractDomain> {
    pub domain: D,
    pub widening_threshold: usize,
    pub narrowing_iterations: usize,
    pub max_iterations: usize,
}

impl<D: AbstractDomain> FixpointEngine<D> {
    /// Create a fixpoint engine for `domain` with conservative defaults.
    ///
    /// The defaults are tuned for small examples:
    /// - widening after `widening_threshold` iterations,
    /// - then `narrowing_iterations` refinement steps,
    /// - with a hard cap of `max_iterations` to avoid accidental non-termination.
    pub fn new(domain: D) -> Self {
        Self {
            domain,
            widening_threshold: 3,
            narrowing_iterations: 2,
            max_iterations: 1000,
        }
    }

    /// Compute least fixpoint: `µX. F(X) ⊔ init`
    ///
    /// Uses widening after threshold to ensure termination.
    pub fn lfp<F>(&self, init: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        let mut x = init.clone();
        let mut iterations = 0;

        log::debug!("Starting fixpoint computation");
        log::debug!("  Initial: {:?}", init);

        loop {
            let fx = f(&x);
            log::debug!("  Iteration {}: f(x) = {:?}", iterations + 1, fx);

            let next = self.domain.join(&init, &fx);
            log::debug!("  Iteration {}: join(init, f(x)) = {:?}", iterations + 1, next);

            if self.domain.le(&next, &x) {
                // Fixpoint reached
                log::debug!("  Fixpoint reached: next ⊑ x");
                break;
            }

            iterations += 1;

            if iterations >= self.widening_threshold {
                // Apply widening
                let widened = self.domain.widen(&x, &next);
                log::debug!("  Iteration {}: widening x ∇ next = {:?}", iterations, widened);
                x = widened;
            } else {
                log::debug!("  Iteration {}: x := next", iterations);
                x = next;
            }

            // Safety: prevent infinite loops
            if iterations > self.max_iterations {
                log::warn!("Fixpoint computation did not converge after {} iterations", self.max_iterations);
                break;
            }
        }

        log::debug!("Fixpoint converged after {} iterations: {:?}", iterations, x);

        // Optional: narrowing phase for precision
        if self.narrowing_iterations > 0 {
            log::debug!("Starting narrowing phase");
            self.narrow(x, f)
        } else {
            x
        }
    }

    /// Narrowing phase to refine over-approximation.
    ///
    /// Conceptually, this applies a few steps of `x := x △ f(x)` to claw back
    /// precision lost to widening.
    fn narrow<F>(&self, mut x: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        for i in 0..self.narrowing_iterations {
            let fx = f(&x);
            log::debug!("  Narrowing {}: f(x) = {:?}", i + 1, fx);

            let next = self.domain.narrow(&x, &fx);
            log::debug!("  Narrowing {}: narrow(x, f(x)) = {:?}", i + 1, next);

            if self.domain.le(&x, &next) {
                log::debug!("  Narrowing converged after {} iterations", i + 1);
                break;
            }

            x = next;
        }

        log::debug!("Narrowing complete: {:?}", x);
        x
    }

    /// Compute greatest fixpoint: `νX. F(X) ⊓ init`
    ///
    /// For safety properties and backward analysis.
    pub fn gfp<F>(&self, init: D::Element, f: F) -> D::Element
    where
        F: Fn(&D::Element) -> D::Element,
    {
        let mut x = init.clone();
        let mut iterations = 0;

        loop {
            let fx = f(&x);
            let next = self.domain.meet(&init, &fx);

            if self.domain.le(&x, &next) {
                break;
            }

            x = next;
            iterations += 1;

            if iterations > self.max_iterations {
                log::warn!("GFP computation did not converge after {} iterations", self.max_iterations);
                break;
            }
        }

        log::debug!("Greatest fixpoint converged after {} iterations", iterations);
        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // We define a simple ad-hoc domain for testing fixpoint logic
    // without depending on complex domains like Interval or PointsTo.
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum AdHocElement {
        Bottom,
        Val(i32),
        Top,
    }

    #[derive(Debug, Clone)]
    struct AdHocDomain;

    impl AbstractDomain for AdHocDomain {
        type Element = AdHocElement;

        fn bottom(&self) -> Self::Element {
            AdHocElement::Bottom
        }

        fn top(&self) -> Self::Element {
            AdHocElement::Top
        }

        fn is_bottom(&self, elem: &Self::Element) -> bool {
            matches!(elem, AdHocElement::Bottom)
        }

        fn is_top(&self, elem: &Self::Element) -> bool {
            matches!(elem, AdHocElement::Top)
        }

        fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
            match (elem1, elem2) {
                (AdHocElement::Bottom, _) => true,
                (_, AdHocElement::Top) => true,
                (AdHocElement::Val(v1), AdHocElement::Val(v2)) => v1 <= v2,
                _ => false,
            }
        }

        fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
            match (elem1, elem2) {
                (AdHocElement::Bottom, e) | (e, AdHocElement::Bottom) => e.clone(),
                (AdHocElement::Top, _) | (_, AdHocElement::Top) => AdHocElement::Top,
                (AdHocElement::Val(v1), AdHocElement::Val(v2)) => AdHocElement::Val((*v1).max(*v2)),
            }
        }

        fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
            match (elem1, elem2) {
                (AdHocElement::Bottom, _) | (_, AdHocElement::Bottom) => AdHocElement::Bottom,
                (AdHocElement::Top, e) | (e, AdHocElement::Top) => e.clone(),
                (AdHocElement::Val(v1), AdHocElement::Val(v2)) => AdHocElement::Val((*v1).min(*v2)),
            }
        }

        fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
            match (elem1, elem2) {
                (AdHocElement::Val(v1), AdHocElement::Val(v2)) if v2 > v1 => AdHocElement::Top,
                _ => self.join(elem1, elem2),
            }
        }
    }

    #[test]
    fn test_adhoc_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;
        let domain = AdHocDomain;
        let samples = vec![
            AdHocElement::Bottom,
            AdHocElement::Val(0),
            AdHocElement::Val(10),
            AdHocElement::Val(-5),
            AdHocElement::Top,
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_fixpoint_convergence_with_widening() {
        let domain = AdHocDomain;
        let engine = FixpointEngine::new(domain.clone());

        // Initial: 0
        let init = AdHocElement::Val(0);

        // Function: x -> x + 1
        // This creates an ascending chain: 0, 1, 2, ...
        let f = |elem: &AdHocElement| match elem {
            AdHocElement::Val(n) => AdHocElement::Val(n + 1),
            _ => elem.clone(),
        };

        // LFP should reach Top because of widening
        // Iterations:
        // 1. x=0. f(x)=1. join(0,1)=1. 1 !<= 0.
        // 2. x=1. f(x)=2. join(1,2)=2. 2 !<= 1.
        // 3. x=2. f(x)=3. join(2,3)=3. 3 !<= 2.
        // 4. x=3. Threshold reached (default 3). Widen(2, 3) -> Top.
        // 5. x=Top. f(x)=Top. join(Top,Top)=Top. Top <= Top. Fixpoint.
        let lfp = engine.lfp(init, f);
        assert_eq!(lfp, AdHocElement::Top);
    }

    #[test]
    fn test_fixpoint_finite_convergence() {
        let domain = AdHocDomain;
        let mut engine = FixpointEngine::new(domain.clone());
        // Increase threshold so we don't hit widening for this short chain
        engine.widening_threshold = 10;

        // Initial: 0
        let init = AdHocElement::Val(0);

        // Function: x -> min(x + 1, 5)
        let f = |elem: &AdHocElement| match elem {
            AdHocElement::Val(n) => AdHocElement::Val((*n + 1).min(5)),
            _ => elem.clone(),
        };

        // Should converge to 5
        let lfp = engine.lfp(init, f);
        assert_eq!(lfp, AdHocElement::Val(5));
    }
}
