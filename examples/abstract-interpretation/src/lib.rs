//! Abstract interpretation case study.
//!
//! This crate is a self-contained “worked example” of abstract interpretation.
//! It includes:
//! - a tiny imperative AST (expressions, predicates, statements),
//! - a family of abstract domains (numeric and non-numeric),
//! - transfer functions (abstract semantics), and
//! - a fixpoint engine for loops.
//!
//! The code is intentionally direct and explicit: it is meant to be read.
//! The main entry points are [`AbstractDomain`], [`FixpointEngine`], and the AST in [`expr`].
//!
//! # Mental model
//!
//! Abstract interpretation can be read as “execute the program on approximations”.
//! A domain gives you a notion of approximation together with operations to merge paths and to
//! enforce termination.
//!
//! ```text
//! Abstract domain:  (D, ⊑, ⊥, ⊤, ⊔, ⊓, ∇, △)
//! Concrete meaning: γ : D -> P(States)
//!
//! Soundness (informal):
//!   if  d  approximates a set of states,
//!   then ⟦stmt⟧♯(d) approximates the concrete post-states of stmt.
//!
//! Transfer:        ⟦stmt⟧♯ : D -> D
//! Loop invariant:  lfp(F) computed by iteration with widening/narrowing
//! ```
//!
//! The ordering is chosen so that “more precise” means “smaller”:
//! `a ⊑ b` reads as “`a` is at least as precise as `b`”.
//!
//! # What is being analyzed
//!
//! The AST in [`expr`] models a minimal imperative language:
//! - numeric expressions (variables, constants, arithmetic),
//! - boolean predicates over those expressions, and
//! - statements such as assignment, sequencing, conditionals, and while-loops.
//!
//! Most domains in this crate model environments (maps from variables to abstract values).
//! Absent bindings usually mean “unknown” (i.e., behave like `⊤` for that variable).
//!
//! # Path sensitivity (optional)
//!
//! Several domains support path sensitivity by separating:
//! - a *control* component (a symbolic formula over boolean variables), and
//! - a *value* component (intervals, congruences, points-to facts, …).
//!
//! Control can be represented via BDDs ([`bdd_control`]) or SDDs ([`sdd_control`]).
//! The product construction then tracks a set of feasible paths together with a value abstraction.
//!
//! # Module map
//!
//! - [`domain`]: the core [`AbstractDomain`] trait (lattice operations + widening/narrowing).
//! - [`fixpoint`]: [`FixpointEngine`] for computing loop invariants.
//! - [`expr`]: the AST used by the transfer functions.
//! - [`transfer`]/[`numeric`]: transfer interfaces and a baseline numeric transfer.
//! - Numeric domains: [`interval`], [`sign`], [`constant`], [`congruence`].
//! - Control / products: [`bdd_control`], [`sdd_control`], [`product`], [`generic_product`].
//! - Relational / structured examples: [`pointsto`], [`type_domain`], [`automata`], [`string_domain`].
//!
//! # Small examples
//!
//! Constructing a domain and its extremal elements:
//!
//! ```rust
//! use abstract_interpretation::{AbstractDomain, IntervalDomain};
//!
//! let d = IntervalDomain;
//! let bottom = d.bottom();
//! let top = d.top();
//! ```
//!
//! Building a tiny program AST:
//!
//! ```rust
//! use abstract_interpretation::{NumExpr, Stmt};
//!
//! type V = String;
//! type E = NumExpr<V, i64>;
//! type S = Stmt<V>;
//!
//! let prog: S = S::assign("x", E::constant(0)).then(
//!     S::while_stmt(E::var("x").lt(E::constant(10)), S::assign("x", E::var("x").add(E::constant(1)))),
//! );
//! ```
//!
//! See the `examples/` directory for end-to-end analyses.

pub mod automata;
pub mod bdd_control;
pub mod congruence;
pub mod constant;
pub mod domain;
pub mod expr;
pub mod fixpoint;
pub mod generic_product;
pub mod interval;
pub mod numeric;
pub mod pointsto;
pub mod product;
pub mod sdd_control;
pub mod sign;
pub mod string_domain;
pub mod transfer;
pub mod type_domain;

// Re-exports for convenience
pub use automata::{AutomataDomain, CharClass, Predicate, SymbolicDFA, SymbolicNFA};
pub use bdd_control::{BddControlDomain, ControlSensitiveElement, ControlSensitiveProduct, ControlState};
pub use congruence::{Congruence, CongruenceDomain};
pub use constant::{ConstValue, ConstantDomain, ConstantElement};
pub use domain::AbstractDomain;
pub use expr::{NumExpr, NumPred, Stmt};
pub use fixpoint::FixpointEngine;
pub use interval::{Bound, Interval, IntervalDomain, IntervalElement};
pub use numeric::NumericDomain;
pub use pointsto::{Location, LocationMap, PointsToDomain, PointsToElement};
pub use product::{ProductDomain, ProductElement};
pub use sdd_control::{SddControlDomain, SddControlState};
pub use sign::{Sign, SignDomain, SignElement};
pub use string_domain::{
    CharacterSet, CharacterSetDomain, StringConst, StringConstantDomain, StringInclusionDomain, StringLengthDomain, StringPrefixDomain,
    StringSuffixDomain,
};
pub use transfer::{NumericTransferFunction, TransferFunction};
pub use type_domain::{Type, TypeDomain, TypeSet};
