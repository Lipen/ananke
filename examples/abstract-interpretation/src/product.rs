//! Product domain: combines two abstract domains component-wise.

use std::fmt::Debug;

use super::domain::AbstractDomain;

/// Product of two abstract domains.
///
/// The product domain combines a control domain (typically BDD) with
/// a data domain (typically numeric) to enable path-sensitive analysis.
#[derive(Debug, Clone)]
pub struct ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
{
    pub control: C,
    pub numeric: N,
}

/// Element of the product domain.
#[derive(Debug, Clone, PartialEq)]
pub struct ProductElement<C, N> {
    pub control: C,
    pub numeric: N,
}

impl<C, N> ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
{
    /// Create a component-wise product domain.
    ///
    /// This is a *plain* product: `join`, `meet`, `widen`, … are performed
    /// independently on the control and numeric components.
    pub fn new(control: C, numeric: N) -> Self {
        Self { control, numeric }
    }
}

impl<C, N> AbstractDomain for ProductDomain<C, N>
where
    C: AbstractDomain,
    N: AbstractDomain,
    C::Element: Debug + Clone + PartialEq,
    N::Element: Debug + Clone + PartialEq,
{
    type Element = ProductElement<C::Element, N::Element>;

    fn bottom(&self) -> Self::Element {
        ProductElement {
            control: self.control.bottom(),
            numeric: self.numeric.bottom(),
        }
    }

    fn top(&self) -> Self::Element {
        ProductElement {
            control: self.control.top(),
            numeric: self.numeric.top(),
        }
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        self.control.is_bottom(&elem.control) || self.numeric.is_bottom(&elem.numeric)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        self.control.is_top(&elem.control) && self.numeric.is_top(&elem.numeric)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        self.control.le(&elem1.control, &elem2.control) && self.numeric.le(&elem1.numeric, &elem2.numeric)
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.join(&elem1.control, &elem2.control),
            numeric: self.numeric.join(&elem1.numeric, &elem2.numeric),
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.meet(&elem1.control, &elem2.control),
            numeric: self.numeric.meet(&elem1.numeric, &elem2.numeric),
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.widen(&elem1.control, &elem2.control),
            numeric: self.numeric.widen(&elem1.numeric, &elem2.numeric),
        }
    }

    fn narrow(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        ProductElement {
            control: self.control.narrow(&elem1.control, &elem2.control),
            numeric: self.numeric.narrow(&elem1.numeric, &elem2.numeric),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::tests::test_lattice_axioms;
    use crate::interval::IntervalDomain;
    use crate::numeric::NumericDomain;

    // Simple mock domain for testing product
    #[derive(Debug, Clone)]
    struct SimpleDomain;

    #[derive(Debug, Clone, PartialEq)]
    enum SimpleElement {
        Bottom,
        A,
        B,
        AB,
        Top,
    }

    impl AbstractDomain for SimpleDomain {
        type Element = SimpleElement;

        fn bottom(&self) -> Self::Element {
            SimpleElement::Bottom
        }

        fn top(&self) -> Self::Element {
            SimpleElement::Top
        }

        fn is_bottom(&self, elem: &Self::Element) -> bool {
            matches!(elem, SimpleElement::Bottom)
        }

        fn is_top(&self, elem: &Self::Element) -> bool {
            matches!(elem, SimpleElement::Top)
        }

        fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
            use SimpleElement::*;
            match (elem1, elem2) {
                (Bottom, _) => true,
                (_, Top) => true,
                (A, A) | (A, AB) => true,
                (B, B) | (B, AB) => true,
                (AB, AB) => true,
                _ => false,
            }
        }

        fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
            use SimpleElement::*;
            match (elem1, elem2) {
                (Bottom, e) | (e, Bottom) => e.clone(),
                (Top, _) | (_, Top) => Top,
                (A, A) => A,
                (B, B) => B,
                (AB, _) | (_, AB) => AB,
                (A, B) | (B, A) => AB,
            }
        }

        fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
            use SimpleElement::*;
            match (elem1, elem2) {
                (Bottom, _) | (_, Bottom) => Bottom,
                (Top, e) | (e, Top) => e.clone(),
                (A, A) => A,
                (B, B) => B,
                (AB, e) | (e, AB) => e.clone(),
                _ => Bottom,
            }
        }

        fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
            // Widening must preserve order: elem1 ⊑ (elem1 ∇ elem2)
            // Simple strategy: use join for widening in this mock domain
            self.join(elem1, elem2)
        }
    }

    #[test]
    fn test_product_domain_operations() {
        let control = SimpleDomain;
        let numeric = IntervalDomain;
        let domain = ProductDomain::new(control, numeric.clone());

        let e1 = ProductElement {
            control: SimpleElement::A,
            numeric: numeric.constant("x", 5),
        };

        let e2 = ProductElement {
            control: SimpleElement::B,
            numeric: numeric.constant("x", 10),
        };

        // Test join
        let joined = domain.join(&e1, &e2);
        assert_eq!(joined.control, SimpleElement::AB);
        assert_eq!(
            joined.numeric.get("x"),
            crate::interval::Interval::new(crate::interval::Bound::Finite(5), crate::interval::Bound::Finite(10))
        );

        // Test bottom
        let bottom = domain.bottom();
        assert!(domain.is_bottom(&bottom));
    }

    #[test]
    fn test_product_lattice_axioms() {
        let control = SimpleDomain;
        let numeric = IntervalDomain;
        let domain = ProductDomain::new(control, numeric.clone());

        // Create sample elements with same variable set
        let x_name = "x".to_string();
        let samples = vec![
            ProductElement {
                control: SimpleElement::Bottom,
                numeric: numeric.bottom(),
            },
            ProductElement {
                control: SimpleElement::A,
                numeric: numeric.constant(&x_name, 0),
            },
            ProductElement {
                control: SimpleElement::B,
                numeric: numeric.constant(&x_name, 5),
            },
            ProductElement {
                control: SimpleElement::AB,
                numeric: numeric.interval(&x_name, 0, 10),
            },
            ProductElement {
                control: SimpleElement::AB,
                numeric: numeric.interval(&x_name, -5, 15),
            },
        ];

        // Validate lattice axioms
        test_lattice_axioms(&domain, &samples);
    }
}
