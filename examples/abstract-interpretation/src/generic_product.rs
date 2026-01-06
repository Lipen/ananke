//! Generic Product Domain.
//!
//! A generic implementation of the Reduced Product of two abstract domains.
//! Allows combining any D1 and D2 (e.g., Interval x Congruence).

use std::fmt::Debug;

use crate::domain::AbstractDomain;

/// Element of a product domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductElement<E1, E2>(pub E1, pub E2);

/// Generic Product Domain.
#[derive(Clone, Debug)]
pub struct ProductDomain<D1, D2> {
    pub d1: D1,
    pub d2: D2,
}

impl<D1, D2> ProductDomain<D1, D2>
where
    D1: AbstractDomain,
    D2: AbstractDomain,
{
    pub fn new(d1: D1, d2: D2) -> Self {
        Self { d1, d2 }
    }

    /// Reduce the product element.
    /// This is where domains exchange information to refine each other.
    /// Default implementation does nothing.
    /// Specific instantiations should override or wrap this.
    pub fn reduce(&self, elem: &mut ProductElement<D1::Element, D2::Element>) {
        // If either is bottom, the whole product is bottom
        if self.d1.is_bottom(&elem.0) || self.d2.is_bottom(&elem.1) {
            elem.0 = self.d1.bottom();
            elem.1 = self.d2.bottom();
        }
    }
}

impl<D1, D2> AbstractDomain for ProductDomain<D1, D2>
where
    D1: AbstractDomain,
    D2: AbstractDomain,
{
    type Element = ProductElement<D1::Element, D2::Element>;

    fn bottom(&self) -> Self::Element {
        ProductElement(self.d1.bottom(), self.d2.bottom())
    }

    fn top(&self) -> Self::Element {
        ProductElement(self.d1.top(), self.d2.top())
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        self.d1.is_bottom(&elem.0) || self.d2.is_bottom(&elem.1)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        self.d1.is_top(&elem.0) && self.d2.is_top(&elem.1)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        self.d1.le(&elem1.0, &elem2.0) && self.d2.le(&elem1.1, &elem2.1)
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let e1 = self.d1.join(&elem1.0, &elem2.0);
        let e2 = self.d2.join(&elem1.1, &elem2.1);
        ProductElement(e1, e2)
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let e1 = self.d1.meet(&elem1.0, &elem2.0);
        let e2 = self.d2.meet(&elem1.1, &elem2.1);

        // Check for bottom after meet
        if self.d1.is_bottom(&e1) || self.d2.is_bottom(&e2) {
            return self.bottom();
        }

        let mut res = ProductElement(e1, e2);
        self.reduce(&mut res);
        res
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let e1 = self.d1.widen(&elem1.0, &elem2.0);
        let e2 = self.d2.widen(&elem1.1, &elem2.1);
        ProductElement(e1, e2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::tests::test_lattice_axioms;
    use crate::interval::IntervalDomain;
    use crate::numeric::NumericDomain;
    use crate::sign::SignDomain;

    #[test]
    fn test_generic_product_lattice_axioms() {
        let d1 = IntervalDomain;
        let d2 = SignDomain;
        let product = ProductDomain::new(d1.clone(), d2.clone());

        // Create sample elements
        let i_top = d1.top();
        let i_const = d1.constant("x", 5);

        let s_top = d2.top();
        let s_pos = d2.constant("x", 5);

        let samples = vec![
            product.bottom(),
            product.top(),
            ProductElement(i_const.clone(), s_pos.clone()),
            ProductElement(i_top.clone(), s_pos.clone()),
            ProductElement(i_const.clone(), s_top.clone()),
        ];

        test_lattice_axioms(&product, &samples);
    }
}
